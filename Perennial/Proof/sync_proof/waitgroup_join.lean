/-
The "join" idiom for
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

structure WaitGroupJoinNames where
  wgGn : WaitGroupNames
  wgApropGn : GName
  wgNotDoneGn : GName

abbrev wgjN : Namespace := nroot.@"wgjoin"

section waitgroup_join_idiom
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The body of the internal invariant. Maintains ownership of the waitgroup
counter so that `Done()` can run concurrently to `Add`. -/
abbrev wgjInv (γ : WaitGroupJoinNames) : IProp GF :=
  iprop(∃ (ctr : w32) (added done : Nat) (Pdone : IProp GF),
    "Hwg_ctr" ∷ ownWaitGroup γ.wgGn ctr ∗
    "Hadded" ∷ ownTokAuthDfrac γ.wgNotDoneGn (DFrac.own (1 : Qp).half) added ∗
    "Hdone_toks" ∷ ownToks γ.wgNotDoneGn done ∗
    "Hdone_aprop" ∷ ownApropFrag γ.wgApropGn Pdone done ∗
    "Hdone_P" ∷ Pdone ∗
    "%Hctr_pos" ∷ ⌜0 ≤ sint.Z ctr⌝ ∗
    "%Hctr" ∷ ⌜sint.Z ctr = (added : Int) - (done : Int)⌝)

abbrev isWgjInv (wg : Loc) (γ : WaitGroupJoinNames) : IProp GF :=
  iprop("#His" ∷ isWaitGroup wg γ.wgGn (wgjN.@"wg") ∗
    "#Hinv" ∷ inv (wgjN.@"inv") (wgjInv γ))

/-- Permission to call `Add` or `Wait`. Calling `Add` will extend `P` with a
caller-chosen proposition (as long as `num_added` doesn't overflow) and calling
`Wait` will give `P` as postcondition and reset the permission. -/
def ownAdderDef (wg : Loc) (num_added : w32) (P : IProp GF) : IProp GF :=
  iprop(∃ (γ : WaitGroupJoinNames) (P' : IProp GF),
    "Hno_waiters" ∷ ownWaitGroupWaiters γ.wgGn 0 ∗
    "Haprop" ∷ ownApropAuth γ.wgApropGn P' (sint.nat num_added) ∗
    "Hadded" ∷ ownTokAuthDfrac γ.wgNotDoneGn (DFrac.own (1 : Qp).half) (sint.nat num_added) ∗
    "%Hadded_pos" ∷ ⌜0 ≤ sint.Z num_added⌝ ∗
    "HimpliesP" ∷ (P' -∗ P) ∗
    "#Hinv" ∷ isWgjInv wg γ)
@[irreducible] def ownAdder (wg : Loc) (num_added : w32) (P : IProp GF) : IProp GF :=
  ownAdderDef wg num_added P
theorem ownAdder_unseal : @ownAdder = @ownAdderDef := by funext; with_unfolding_all rfl

/-- Permission to call `Done` as long as `P` is passed in. -/
def ownDoneDef (wg : Loc) (P : IProp GF) : IProp GF :=
  iprop(∃ (γ : WaitGroupJoinNames),
    "Haprop" ∷ ownAprop γ.wgApropGn P ∗
    "Hdone_tok" ∷ ownToks γ.wgNotDoneGn 1 ∗
    "#Hinv" ∷ isWgjInv wg γ)
@[irreducible] def ownDone (wg : Loc) (P : IProp GF) : IProp GF := ownDoneDef wg P
theorem ownDone_unseal : @ownDone = @ownDoneDef := by funext; with_unfolding_all rfl

theorem ownTokAuth_halves (γ : GName) (n : Nat) :
    ownTokAuth (GF := GF) γ n ⊣⊢
      ownTokAuthDfrac γ (DFrac.own (1 : Qp).half) n ∗
      ownTokAuthDfrac γ (DFrac.own (1 : Qp).half) n := by
  have h := (ownTokAuth_fractional (GF := GF) γ n).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

theorem init (wg : Loc) (γwg : WaitGroupNames) :
    isWaitGroup (GF := GF) wg γwg (wgjN.@"wg") ∗ ownWaitGroup γwg (W32 0) ∗
      ownWaitGroupWaiters γwg 0 ⊢ |={⊤}=> ownAdder wg (W32 0) iprop(True) := by
  iintro ⟨#His, Hctr_inv, Hwaiters⟩
  imod ownApropAuth_alloc (GF := GF) with ⟨%wgApropGn, Haprop⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%wgNotDoneGn, Hadded⟩
  icases (ownTokAuth_halves wgNotDoneGn 0).1 $$ Hadded with ⟨Hadded_inv, Hadded⟩
  imod ownToks_0 (GF := GF) wgNotDoneGn with Htoks
  ihave Hfrag := ownApropFrag_0 (GF := GF) wgApropGn
  let γ : WaitGroupJoinNames := ⟨γwg, wgApropGn, wgNotDoneGn⟩
  imod inv_alloc (wgjN.@"inv") ⊤ (wgjInv (GF := GF) γ) $$ [Hctr_inv Hadded_inv Htoks Hfrag] with #Hinv
  · inext
    iexists (W32 0), 0, 0, iprop(True)
    simp only [γ]
    iframe
    isplitr
    · itrivial
    ipureintro
    exact ⟨by decide, by decide⟩
  imodintro
  simp only [ownAdder_unseal, ownAdderDef]
  iexists γ, iprop(True)
  simp only [show sint.nat (W32 0) = 0 from rfl, γ]
  iframe
  isplitr
  · ipureintro; decide
  isplitr
  · iintro _; itrivial
  unfold isWgjInv named
  isplit <;> iassumption

theorem WaitGroup.wp_Add (P' : IProp GF) (wg : Loc) (P : IProp GF) (num_added : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder wg num_added P ∗
        ⌜sint.Z num_added < 2 ^ 31 - 1⌝ }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); ownAdder wg (num_added + W32 1) iprop(P ∗ P') ∗ ownDone wg P' }} := by
  wp_start_folded as ⟨Ha, %Hoverflow⟩
  simp only [ownAdder_unseal, ownAdderDef]
  icases Ha with ⟨%γ, %P0, Ha⟩
  iNamed Ha
  iNamed Hinv
  wp_apply_core sync.WaitGroup.wp_Add wg (W64 1) γ.wgGn (wgjN.@"wg") $$ [] [-]
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
  imod ownApropAuth_add P' γ.wgApropGn P0 (sint.nat num_added) $$ Haprop with ⟨Haprop, Hdone_aprop⟩
  ihave Hadded := (ownTokAuth_halves γ.wgNotDoneGn (sint.nat num_added)).2 $$ [Hadded Hadded_inv]
  · iframe
  imod ownTokAuth_S γ.wgNotDoneGn _ $$ Hadded with ⟨Hadded, Hdone_tok⟩
  icases (ownTokAuth_halves γ.wgNotDoneGn _).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
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
  simp only [ownAdder_unseal, ownAdderDef, ownDone_unseal, ownDoneDef]
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
    unfold isWgjInv named
    isplit <;> iassumption
  · iexists γ
    iframe
    unfold isWgjInv named
    isplit <;> iassumption

theorem WaitGroup.wp_Done (P : IProp GF) (wg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownDone wg P ∗ P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); True }} := by
  wp_start_folded as ⟨Ha, HP⟩
  simp only [ownDone_unseal, ownDoneDef]
  icases Ha with ⟨%γ, Ha⟩
  iNamed Ha
  iNamed Hinv
  wp_apply_core sync.WaitGroup.wp_Done wg γ.wgGn (wgjN.@"wg") $$ [] [-]
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

theorem WaitGroup.wp_Wait (P : IProp GF) (n : w32) (wg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder wg n P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); ▷ P ∗ ownAdder wg (W32 0) iprop(True) }} := by
  wp_start_folded as Ha
  iapply wp_fupd
  simp only [ownAdder_unseal, ownAdderDef]
  icases Ha with ⟨%γ, %P0, Ha⟩
  iNamed Ha
  iNamed Hinv
  iapply fupd_wp
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑(wgjN.@"wg")) (fun _ _ => CoPset.mem_full) with Hmask
  imod alloc_wait_token wg γ.wgGn (wgjN.@"wg") 0 (by decide) $$ His Hno_waiters with ⟨Hwaiter, Htok⟩
  imod Hmask with -
  imodintro
  wp_apply_core sync.WaitGroup.wp_Wait wg γ.wgGn (wgjN.@"wg") $$ [Htok] [-]
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
  imod ownApropAuth_reset γ.wgApropGn P0 Pdone _ $$ Haprop Hdone_aprop_inv with Haprop
  ihave Hadded := (ownTokAuth_halves γ.wgNotDoneGn _).2 $$ [Hadded Hadded_inv]
  · iframe
  imod ownTokAuth_sub _ γ.wgNotDoneGn _ $$ Hadded Hdone_toks_inv with Hadded
  rw [Nat.sub_self]
  icases (ownTokAuth_halves γ.wgNotDoneGn 0).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  imod Hmask with -
  ihave Hfrag := ownApropFrag_0 (GF := GF) γ.wgApropGn
  imod ownToks_0 (GF := GF) γ.wgNotDoneGn with Hdone_toks_inv
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
  imod dealloc_wait_token wg γ.wgGn (wgjN.@"wg") (0 + 1) (by decide) $$ His Hwaiter Hwt with H
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
  unfold isWgjInv named
  isplit <;> iassumption

theorem ownAdder_wand (P' : IProp GF) (wg : Loc) (n : w32) (P : IProp GF) :
    ⊢ (P -∗ P') -∗ ownAdder wg n P -∗ ownAdder wg n P' := by
  iintro Hwand Ha
  simp only [ownAdder_unseal, ownAdderDef]
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
