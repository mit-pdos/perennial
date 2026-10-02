/-
Port of `new/proof/sync_proof/waitgroup_join.v`: the "join" idiom for
`WaitGroup`: `Add` hands out permission to call `Done` with a chosen
proposition, and `Wait` collects all of them.
-/
import Perennial.Proof.sync_proof.base
import Perennial.Proof.sync_proof.waitgroup

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

namespace join

structure WaitGroup_join_names where
  wg_gn : WaitGroup_names
  wg_aprop_gn : GName
  wg_not_done_gn : GName

/-- Rocq `wgjN` (local). -/
abbrev wgjN : Namespace := nroot.@"wgjoin"

section waitgroup_join_idiom
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The body of the internal invariant. Maintains ownership of the waitgroup
counter so that `Done()` can run concurrently to `Add`. -/
abbrev wgj_inv (γ : WaitGroup_join_names) : IProp GF :=
  iprop(∃ (ctr : w32) (added done : Nat) (Pdone : IProp GF),
    "Hwg_ctr" ∷ own_WaitGroup γ.wg_gn ctr ∗
    "Hadded" ∷ own_tok_auth_dfrac γ.wg_not_done_gn (DFrac.own (1 : Qp).half) added ∗
    "Hdone_toks" ∷ own_toks γ.wg_not_done_gn done ∗
    "Hdone_aprop" ∷ own_aprop_frag γ.wg_aprop_gn Pdone done ∗
    "Hdone_P" ∷ Pdone ∗
    "%Hctr_pos" ∷ ⌜0 ≤ sint.Z ctr⌝ ∗
    "%Hctr" ∷ ⌜sint.Z ctr = (added : Int) - (done : Int)⌝)

/-- Rocq `is_wgj_inv` (local). -/
abbrev is_wgj_inv (wg : loc) (γ : WaitGroup_join_names) : IProp GF :=
  iprop("#His" ∷ is_WaitGroup wg γ.wg_gn (wgjN.@"wg") ∗
    "#Hinv" ∷ inv (wgjN.@"inv") (wgj_inv γ))

/-- Permission to call `Add` or `Wait`. Calling `Add` will extend `P` with a
caller-chosen proposition (as long as `num_added` doesn't overflow) and calling
`Wait` will give `P` as postcondition and reset the permission. -/
def own_Adder_def (wg : loc) (num_added : w32) (P : IProp GF) : IProp GF :=
  iprop(∃ (γ : WaitGroup_join_names) (P' : IProp GF),
    "Hno_waiters" ∷ own_WaitGroup_waiters γ.wg_gn 0 ∗
    "Haprop" ∷ own_aprop_auth γ.wg_aprop_gn P' (sint.nat num_added) ∗
    "Hadded" ∷ own_tok_auth_dfrac γ.wg_not_done_gn (DFrac.own (1 : Qp).half) (sint.nat num_added) ∗
    "%Hadded_pos" ∷ ⌜0 ≤ sint.Z num_added⌝ ∗
    "HimpliesP" ∷ (P' -∗ P) ∗
    "#Hinv" ∷ is_wgj_inv wg γ)
@[irreducible] def own_Adder (wg : loc) (num_added : w32) (P : IProp GF) : IProp GF :=
  own_Adder_def wg num_added P
theorem own_Adder_unseal : @own_Adder = @own_Adder_def := by funext; with_unfolding_all rfl

/-- Permission to call `Done` as long as `P` is passed in. -/
def own_Done_def (wg : loc) (P : IProp GF) : IProp GF :=
  iprop(∃ (γ : WaitGroup_join_names),
    "Haprop" ∷ own_aprop γ.wg_aprop_gn P ∗
    "Hdone_tok" ∷ own_toks γ.wg_not_done_gn 1 ∗
    "#Hinv" ∷ is_wgj_inv wg γ)
@[irreducible] def own_Done (wg : loc) (P : IProp GF) : IProp GF := own_Done_def wg P
theorem own_Done_unseal : @own_Done = @own_Done_def := by funext; with_unfolding_all rfl

theorem own_tok_auth_halves (γ : GName) (n : Nat) :
    own_tok_auth (GF := GF) γ n ⊣⊢
      own_tok_auth_dfrac γ (DFrac.own (1 : Qp).half) n ∗
      own_tok_auth_dfrac γ (DFrac.own (1 : Qp).half) n := by
  have h := (own_tok_auth_fractional (GF := GF) γ n).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

theorem init (wg : loc) (γwg : WaitGroup_names) :
    is_WaitGroup (GF := GF) wg γwg (wgjN.@"wg") ∗ own_WaitGroup γwg (W32 0) ∗
      own_WaitGroup_waiters γwg 0 ⊢ |={⊤}=> own_Adder wg (W32 0) iprop(True) := by
  iintro ⟨#His, Hctr_inv, Hwaiters⟩
  imod own_aprop_auth_alloc (GF := GF) with ⟨%wg_aprop_gn, Haprop⟩
  imod own_tok_auth_alloc (GF := GF) with ⟨%wg_not_done_gn, Hadded⟩
  icases (own_tok_auth_halves wg_not_done_gn 0).1 $$ Hadded with ⟨Hadded_inv, Hadded⟩
  imod own_toks_0 (GF := GF) wg_not_done_gn with Htoks
  ihave Hfrag := own_aprop_frag_0 (GF := GF) wg_aprop_gn
  let γ : WaitGroup_join_names := ⟨γwg, wg_aprop_gn, wg_not_done_gn⟩
  imod inv_alloc (wgjN.@"inv") ⊤ (wgj_inv (GF := GF) γ) $$ [Hctr_inv Hadded_inv Htoks Hfrag] with #Hinv
  · inext
    iexists (W32 0), 0, 0, iprop(True)
    simp only [γ]
    iframe
    isplitr
    · itrivial
    ipureintro
    exact ⟨by decide, by decide⟩
  imodintro
  simp only [own_Adder_unseal, own_Adder_def]
  iexists γ, iprop(True)
  simp only [show sint.nat (W32 0) = 0 from rfl, γ]
  iframe
  isplitr
  · ipureintro; decide
  isplitr
  · iintro _; itrivial
  unfold is_wgj_inv named
  isplit <;> iassumption

theorem wp_WaitGroup__Add (P' : IProp GF) (wg : loc) (P : IProp GF) (num_added : w32) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ own_Adder wg num_added P ∗
        ⌜sint.Z num_added < 2 ^ 31 - 1⌝ }}
      (App (Val (wg @!! go.type.PointerType WaitGroup @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); own_Adder wg (num_added + W32 1) iprop(P ∗ P') ∗ own_Done wg P' }} := by
  wp_start_folded as ⟨Ha, %Hoverflow⟩
  simp only [own_Adder_unseal, own_Adder_def]
  icases Ha with ⟨%γ, %P0, Ha⟩
  iNamed Ha
  iNamed Hinv
  wp_apply_core sync.wp_WaitGroup__Add wg (W64 1) γ.wg_gn (wgjN.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne wgjN "wg" "inv" (by decide))
  iintro Hmask
  inext
  icases Hi with ⟨%ctr, %added, %done, %Pdone, Hi⟩
  iNamedSuffix Hi "_inv"
  iexists ctr
  iframe Hwg_ctr_inv
  icombine Hadded Hadded_inv gives % ⟨_, Heq⟩
  subst Heq
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have h2 : W32 (sint.Z (W64 1)) = W32 1 := by decide
  rw [h1, h2]
  isplitr
  · ipureintro
    simp only [sint.nat, sint.Z] at *
    omega
  iright
  iframe Hno_waiters
  iintro Hno_waiters Hwg_ctr_inv
  imod Hmask with -
  imod own_aprop_auth_add P' γ.wg_aprop_gn P0 (sint.nat num_added) $$ Haprop with ⟨Haprop, Hdone_aprop⟩
  ihave Hadded := (own_tok_auth_halves γ.wg_not_done_gn (sint.nat num_added)).2 $$ [Hadded Hadded_inv]
  · iframe
  imod own_tok_auth_S γ.wg_not_done_gn _ $$ Hadded with ⟨Hadded, Hdone_tok⟩
  icases (own_tok_auth_halves γ.wg_not_done_gn _).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  have hn : sint.nat (num_added + W32 1) = sint.nat num_added + 1 := by
    simp only [sint.nat] at *; word
  imod Hclose $$ [Hwg_ctr_inv Hadded_inv Hdone_toks_inv Hdone_aprop_inv Hdone_P_inv] with -
  · inext
    iexists (ctr + W32 1), (sint.nat num_added + 1), done, Pdone
    iframe
    ipureintro
    simp only [sint.nat] at *
    constructor <;> word
  imodintro
  iapply HΦ
  simp only [own_Adder_unseal, own_Adder_def, own_Done_unseal, own_Done_def]
  isplitl [Hno_waiters Haprop Hadded HimpliesP]
  · iexists γ, iprop(P0 ∗ P')
    rw [hn]
    iframe
    isplitr
    · ipureintro; simp only [sint.nat] at *; word
    isplitl
    · iintro ⟨H1, H2⟩
      iframe H2
      iapply HimpliesP $$ H1
    unfold is_wgj_inv named
    isplit <;> iassumption
  · iexists γ
    iframe
    unfold is_wgj_inv named
    isplit <;> iassumption

theorem wp_WaitGroup__Done (P : IProp GF) (wg : loc) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ own_Done wg P ∗ P }}
      (App (Val (wg @!! go.type.PointerType WaitGroup @!! go!"Done")) (Val #()))
    {{ RET #(); True }} := by
  wp_start_folded as ⟨Ha, HP⟩
  simp only [own_Done_unseal, own_Done_def]
  icases Ha with ⟨%γ, Ha⟩
  iNamed Ha
  iNamed Hinv
  wp_apply_core sync.wp_WaitGroup__Done wg γ.wg_gn (wgjN.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne wgjN "wg" "inv" (by decide))
  iintro Hmask
  inext
  icases Hi with ⟨%ctr, %added, %done, %Pdone, Hi⟩
  iNamedSuffix Hi "_inv"
  iexists ctr
  iframe Hwg_ctr_inv
  icombine Hdone_tok Hdone_toks_inv as Hdone_toks_inv
  icombine Haprop Hdone_aprop_inv as Hdone_aprop_inv
  icombine Hadded_inv Hdone_toks_inv gives %Hle
  isplitr
  · ipureintro; word
  iintro Hwg_ctr_inv
  imod Hmask with -
  imod Hclose $$ [Hwg_ctr_inv Hadded_inv Hdone_toks_inv Hdone_aprop_inv Hdone_P_inv HP] with -
  · inext
    iexists (ctr - W32 1), added, (1 + done), iprop(P ∗ Pdone)
    iframe Hwg_ctr_inv Hadded_inv Hdone_aprop_inv
    rw [Nat.add_comm 1 done]
    iframe Hdone_toks_inv
    isplitl [HP Hdone_P_inv]
    · unfold named; isplitl [HP]
      · iexact HP
      · iexact Hdone_P_inv
    ipureintro
    constructor <;> word
  imodintro
  iapply HΦ
  itrivial

theorem wp_WaitGroup__Wait (P : IProp GF) (n : w32) (wg : loc) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ own_Adder wg n P }}
      (App (Val (wg @!! go.type.PointerType WaitGroup @!! go!"Wait")) (Val #()))
    {{ RET #(); ▷ P ∗ own_Adder wg (W32 0) iprop(True) }} := by
  wp_start_folded as Ha
  iapply wp_fupd
  simp only [own_Adder_unseal, own_Adder_def]
  icases Ha with ⟨%γ, %P0, Ha⟩
  iNamed Ha
  iNamed Hinv
  iapply fupd_wp
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑(wgjN.@"wg")) (fun _ _ => CoPset.mem_full) with Hmask
  imod alloc_wait_token wg γ.wg_gn (wgjN.@"wg") 0 (by decide) $$ His Hno_waiters with ⟨Hwaiter, Htok⟩
  imod Hmask with -
  imodintro
  wp_apply_core sync.wp_WaitGroup__Wait wg γ.wg_gn (wgjN.@"wg") $$ [Htok] [-]
  · iframe #; iframe
  imod inv_acc (E := ⊤ \ ↑(wgjN.@"wg")) (wg_mask_ndot_ne wgjN "inv" "wg" (by decide)) $$ Hinv
    with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hi with ⟨%ctr, %added, %done, %Pdone, Hi⟩
  iNamedSuffix Hi "_inv"
  iexists ctr
  iframe Hwg_ctr_inv
  iintro %Hctr_zero Hwg_ctr_inv
  have hctr : ctr = W32 0 := by
    apply BitVec.eq_of_toInt_eq; simpa [sint.Z] using Hctr_zero
  subst hctr
  have hdone : added = done := by simp only [show sint.Z (W32 0) = 0 from rfl] at Hctr_inv; omega
  subst hdone
  icombine Hadded Hadded_inv gives % ⟨_, Heq⟩
  rw [← Heq]
  icombine Hdone_aprop_inv Haprop gives #HPeq
  imod own_aprop_auth_reset γ.wg_aprop_gn P0 Pdone _ $$ Haprop Hdone_aprop_inv with Haprop
  ihave Hadded := (own_tok_auth_halves γ.wg_not_done_gn _).2 $$ [Hadded Hadded_inv]
  · iframe
  imod own_tok_auth_sub _ γ.wg_not_done_gn _ $$ Hadded Hdone_toks_inv with Hadded
  rw [Nat.sub_self]
  icases (own_tok_auth_halves γ.wg_not_done_gn 0).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  imod Hmask with -
  ihave Hfrag := own_aprop_frag_0 (GF := GF) γ.wg_aprop_gn
  imod own_toks_0 (GF := GF) γ.wg_not_done_gn with Hdone_toks_inv
  imod Hclose $$ [Hwg_ctr_inv Hadded_inv Hdone_toks_inv Hfrag] with -
  · inext
    iexists (W32 0), 0, 0, iprop(True)
    iframe
    iframe #
    isplitr
    · itrivial
    ipureintro
    exact ⟨by decide, by decide⟩
  imodintro
  iintro Hwt
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑(wgjN.@"wg")) (fun _ _ => CoPset.mem_full) with Hmask
  imod dealloc_wait_token wg γ.wg_gn (wgjN.@"wg") (0 + 1) (by decide) $$ His Hwaiter Hwt with H
  imod Hmask with -
  imodintro
  iapply HΦ
  isplitl [Hdone_P_inv HimpliesP]
  · icases HPeq with ⟨HPa, HPb⟩
    ihave H : (▷ P0 : IProp GF) $$ [Hdone_P_inv]
    · iapply HPa
      inext
      iexact Hdone_P_inv
    inext
    iapply HimpliesP $$ H
  iexists γ, iprop(True)
  simp only [show sint.nat (W32 0) = 0 from rfl, show (0 : Int) + 1 - 1 = 0 from rfl]
  iframe
  isplitr
  · ipureintro; decide
  isplitr
  · iintro _; itrivial
  unfold is_wgj_inv named
  isplit <;> iassumption

theorem own_Adder_wand (P' : IProp GF) (wg : loc) (n : w32) (P : IProp GF) :
    ⊢ (P -∗ P') -∗ own_Adder wg n P -∗ own_Adder wg n P' := by
  iintro Hwand Ha
  simp only [own_Adder_unseal, own_Adder_def]
  icases Ha with ⟨%γ, %P0, Ha⟩
  iNamed Ha
  iexists γ, P0
  iframe
  isplitr
  · ipureintro; exact Hadded_pos
  isplitl
  · iintro H
    iapply Hwand
    iapply HimpliesP $$ H
  iframe #

end waitgroup_join_idiom

end join

end sync

end Perennial
end
