/-
Port of `new/proof/sync_proof/rwmutex_guard.v`: a specification for `RWMutex`
which guards a fractional resource `P q`. `RLock` returns `P rfrac` while
`Lock` returns `P 1`.
-/
import Perennial.Proof.sync_proof.base
import Perennial.Proof.sync_proof.rwmutex

set_option linter.iris.style.nameCheck false
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

/-- Rocq `pos_to_Qp (Z.to_pos z)`: `z` as a positive rational (`1` if `z ≤ 0`). -/
def pos_to_Qp_Z (z : Int) : Qp := ⟨if 0 < z then (z : Rat) else 1, by
  split
  · exact Rat.intCast_pos.mpr ‹_›
  · decide⟩

theorem pos_to_Qp_Z_val (z : Int) (h : 0 < z) : (pos_to_Qp_Z z).val = (z : Rat) := by
  simp [pos_to_Qp_Z, h]

def rfrac_def : Qp := (1 : Qp) / pos_to_Qp_Z (rwmutex.actualMaxReaders + 1)
@[irreducible] def rfrac : Qp := rfrac_def
theorem rfrac_unseal : rfrac = rfrac_def := by with_unfolding_all rfl

theorem actualMaxReaders_pos : 0 < rwmutex.actualMaxReaders := by
  rw [rwmutex.actualMaxReaders_unseal]; decide

/-- The fraction of `P` held by the invariant when there are `n` readers. -/
abbrev inv_frac (n : Nat) : Qp :=
  Qp_mul (pos_to_Qp_Z (rwmutex.actualMaxReaders + 1 - (n : Int))) rfrac

theorem inv_frac_val (n : Nat) (h : (n : Int) ≤ rwmutex.actualMaxReaders) :
    (inv_frac n).val =
      ((rwmutex.actualMaxReaders + 1 - (n : Int) : Int) : Rat) /
        ((rwmutex.actualMaxReaders + 1 : Int) : Rat) := by
  simp only [inv_frac, Qp_mul, rfrac_unseal, rfrac_def, Qp.val_div, Qp.val_one]
  rw [pos_to_Qp_Z_val _ (by omega), pos_to_Qp_Z_val _ (by have := actualMaxReaders_pos; omega)]
  rw [Rat.div_def, Rat.one_mul, Rat.div_def]

theorem inv_frac_S (n : Nat) (h : ((n + 1 : Nat) : Int) ≤ rwmutex.actualMaxReaders) :
    inv_frac n = rfrac + inv_frac (n + 1) := by
  rw [Qp.ext_iff, Qp.val_add, inv_frac_val n (by omega), inv_frac_val (n + 1) h]
  simp only [rfrac_unseal, rfrac_def, Qp.val_div, Qp.val_one]
  rw [pos_to_Qp_Z_val _ (by have := actualMaxReaders_pos; omega)]
  rw [Rat.div_def, Rat.div_def, Rat.div_def, ← Rat.add_mul]
  congr 1
  push_cast
  grind

theorem inv_frac_0 : inv_frac 0 = 1 := by
  rw [Qp.ext_iff, inv_frac_val 0 (by have := actualMaxReaders_pos; omega)]
  rw [show rwmutex.actualMaxReaders + 1 - ((0 : Nat) : Int) = rwmutex.actualMaxReaders + 1 by omega,
    Qp.val_one, Rat.div_def, Rat.mul_inv_cancel]
  have := actualMaxReaders_pos
  exact_mod_cast (show rwmutex.actualMaxReaders + 1 ≠ 0 by omega)

theorem mask_ndot_ne (N : Namespace) (x y : String) (h : x ≠ y) :
    (↑(N.@x) : CoPset) ⊆ ⊤ \ ↑(N.@y) := by
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint N h p ⟨hp, h'⟩⟩

/-- Rocq: `Instance : Inhabited rwmutex` (for destructing `▷ ∃ st, ...`). -/
instance : Inhabited rwmutex := ⟨.Locked⟩

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

namespace rwmutex_guard

/-- The part of the invariant that depends on the `rwmutex` state. -/
def inv_st (P : Qp → IProp GF) (γrlocked γmax γlocked : GName) : rwmutex → IProp GF
  | .Locked => own_tok_auth γrlocked 0
  | .RLocked n => iprop(own_tok_auth γrlocked n ∗ own_toks γmax n ∗
      ghost_var γlocked 1 () ∗ P (inv_frac n))

/-- Rocq `is_inv` (local). -/
abbrev is_inv (P : Qp → IProp GF) (γ : rwmutex.RWMutex_names) (γmax γrlocked γlocked : GName) :
    IProp GF :=
  inv (nroot.@"inv")
    iprop(∃ st, rwmutex.own_RWMutex γ st ∗ inv_st P γrlocked γmax γlocked st)

end rwmutex_guard

open rwmutex_guard in
def own_RWMutex_def (rw : loc) (P : Qp → IProp GF) : IProp GF :=
  iprop(∃ (γ : rwmutex.RWMutex_names) (γmax γrlocked γlocked : GName),
    "Hown" ∷ rwmutex.own_RLock_token γ ∗
    "Hmax" ∷ own_toks γmax 1 ∗
    "#His" ∷ rwmutex.is_RWMutex rw γ (nroot.@"rw") ∗
    "#HPfrac" ∷ □ (∀ q1 q2, P (q1 + q2) ∗-∗ P q1 ∗ P q2) ∗
    "#Hauth" ∷ own_tok_auth_dfrac γmax DFrac.discard (Int.toNat rwmutex.actualMaxReaders) ∗
    "#Hinv" ∷ is_inv P γ γmax γrlocked γlocked)
@[irreducible] def own_RWMutex (rw : loc) (P : Qp → IProp GF) : IProp GF := own_RWMutex_def rw P
theorem own_RWMutex_unseal : @own_RWMutex = @own_RWMutex_def := by funext; with_unfolding_all rfl

open rwmutex_guard in
def own_RWMutex_RLocked_def (rw : loc) (P : Qp → IProp GF) : IProp GF :=
  iprop(∃ (γ : rwmutex.RWMutex_names) (γmax γrlocked γlocked : GName),
    "Hrlocked" ∷ own_toks γrlocked 1 ∗
    "#His" ∷ rwmutex.is_RWMutex rw γ (nroot.@"rw") ∗
    "#HPfrac" ∷ □ (∀ q1 q2, P (q1 + q2) ∗-∗ P q1 ∗ P q2) ∗
    "#Hauth" ∷ own_tok_auth_dfrac γmax DFrac.discard (Int.toNat rwmutex.actualMaxReaders) ∗
    "#Hinv" ∷ is_inv P γ γmax γrlocked γlocked)
@[irreducible] def own_RWMutex_RLocked (rw : loc) (P : Qp → IProp GF) : IProp GF :=
  own_RWMutex_RLocked_def rw P
theorem own_RWMutex_RLocked_unseal : @own_RWMutex_RLocked = @own_RWMutex_RLocked_def := by
  funext; with_unfolding_all rfl

open rwmutex_guard in
def own_RWMutex_Locked_def (rw : loc) (P : Qp → IProp GF) : IProp GF :=
  iprop(∃ (γ : rwmutex.RWMutex_names) (γmax γrlocked γlocked : GName),
    "Hlocked" ∷ ghost_var γlocked 1 () ∗
    "Hown_rlock" ∷ rwmutex.own_RLock_token γ ∗
    "Hmax" ∷ own_toks γmax 1 ∗
    "#His" ∷ rwmutex.is_RWMutex rw γ (nroot.@"rw") ∗
    "#HPfrac" ∷ □ (∀ q1 q2, P (q1 + q2) ∗-∗ P q1 ∗ P q2) ∗
    "#Hauth" ∷ own_tok_auth_dfrac γmax DFrac.discard (Int.toNat rwmutex.actualMaxReaders) ∗
    "#Hinv" ∷ is_inv P γ γmax γrlocked γlocked)
@[irreducible] def own_RWMutex_Locked (rw : loc) (P : Qp → IProp GF) : IProp GF :=
  own_RWMutex_Locked_def rw P
theorem own_RWMutex_Locked_unseal : @own_RWMutex_Locked = @own_RWMutex_Locked_def := by
  funext; with_unfolding_all rfl

open rwmutex_guard

theorem wp_RWMutex__RLock (rw : loc) (P : Qp → IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ own_RWMutex rw P }}
      (App (Val (rw @!! go.type.PointerType RWMutex @!! go!"RLock")) (Val #()))
    {{ RET #(); own_RWMutex_RLocked rw P ∗ ▷ P rfrac }} := by
  wp_start_folded as Hpre
  simp only [own_RWMutex_unseal, own_RWMutex_def]
  icases Hpre with ⟨%γ, %γmax, %γrlocked, %γlocked, Hpre⟩
  iNamed Hpre
  wp_apply_core rwmutex.wp_RWMutex__RLock γ rw (nroot.@"rw") $$ [Hown] [-]
  · iframe #; iframe
  iinv Hinv with Hi Hclose <;> try exact ⟨mask_ndot_ne nroot "inv" "rw" (by decide), trivial⟩
  icases Hi with ⟨%st, >Hst, HP⟩
  iframe Hst
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iintro %n %Hst' H
  subst Hst'
  simp only [inv_st]
  icases HP with ⟨>Hrtok, >Htoks, Hl, HP⟩
  icombine Htoks Hmax as Htoks
  icombine Hauth Htoks gives %Hle
  rw [inv_frac_S n (by omega)]
  imod own_tok_auth_add 1 γrlocked n $$ Hrtok with ⟨Hrtok, Ht⟩
  icases HPfrac $$ HP with ⟨HP', HP⟩
  imod Hmask with _
  imod Hclose $$ [Hrtok Htoks Hl HP H] with _
  · inext
    iexists (rwmutex.RLocked (n + 1))
    iframe H
    simp only [inv_st]
    iframe
  imodintro
  iapply HΦ
  simp only [own_RWMutex_RLocked_unseal, own_RWMutex_RLocked_def]
  iframe HP'
  iexists γ, γmax, γrlocked, γlocked
  iframe Ht
  iframe #

theorem wp_RWMutex__RUnlock (rw : loc) (P : Qp → IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ own_RWMutex_RLocked rw P ∗ ▷ P rfrac }}
      (App (Val (rw @!! go.type.PointerType RWMutex @!! go!"RUnlock")) (Val #()))
    {{ RET #(); own_RWMutex rw P }} := by
  wp_start_folded as ⟨Ho, HP_in⟩
  simp only [own_RWMutex_RLocked_unseal, own_RWMutex_RLocked_def]
  icases Ho with ⟨%γ, %γmax, %γrlocked, %γlocked, Ho⟩
  iNamed Ho
  wp_apply_core rwmutex.wp_RWMutex__RUnlock γ rw (nroot.@"rw") $$ [] [-]
  · iframe #
  iinv Hinv with Hi Hclose <;> try exact ⟨mask_ndot_ne nroot "inv" "rw" (by decide), trivial⟩
  icases Hi with ⟨%st, >Hst, HP⟩
  cases st with
  | Locked =>
    simp only [inv_st]
    icases HP with >HP
    icombine HP Hrlocked gives %Hbad
    omega
  | RLocked n =>
  simp only [inv_st]
  icases HP with ⟨>Hrauth, >Htoks, Hl, HP⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  icombine Hrauth Hrlocked gives %Hle
  icombine Hauth Htoks gives %Hmaxle
  iexists (n - 1)
  rw [show n - 1 + 1 = n by omega]
  iframe Hst
  iintro ⟨Hst, Hrlock⟩
  imod own_tok_auth_sub 1 γrlocked n $$ Hrauth Hrlocked with Hrauth
  icases own_toks_add_1 1 (n - 1) γmax $$ [Htoks] with ⟨Htoks, Htok⟩
  · rw [show n - 1 + 1 = n by omega]; iexact Htoks
  imod Hmask with _
  imod Hclose $$ [Hst Hrauth Htoks Hl HP HP_in] with _
  · inext
    iexists (rwmutex.RLocked (n - 1))
    iframe Hst
    simp only [inv_st]
    iframe
    ihave HP := HPfrac $$ %rfrac %(inv_frac n) [HP HP_in]
    · iframe
    rw [inv_frac_S (n - 1) (by omega), show n - 1 + 1 = n by omega]
    iexact HP
  imodintro
  iapply HΦ
  simp only [own_RWMutex_unseal, own_RWMutex_def]
  iexists γ, γmax, γrlocked, γlocked
  iframe Hrlock Htok
  iframe #

theorem wp_RWMutex__Lock (rw : loc) (P : Qp → IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ own_RWMutex rw P }}
      (App (Val (rw @!! go.type.PointerType RWMutex @!! go!"Lock")) (Val #()))
    {{ RET #(); own_RWMutex_Locked rw P ∗ ▷ P 1 }} := by
  wp_start_folded as Ho
  simp only [own_RWMutex_unseal, own_RWMutex_def]
  icases Ho with ⟨%γ, %γmax, %γrlocked, %γlocked, Ho⟩
  iNamed Ho
  wp_apply_core rwmutex.wp_RWMutex__Lock γ rw (nroot.@"rw") $$ [] [-]
  · iframe #
  iinv Hinv with Hi Hclose <;> try exact ⟨mask_ndot_ne nroot "inv" "rw" (by decide), trivial⟩
  icases Hi with ⟨%st, >Hst, HP⟩
  iframe Hst
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iintro %Hst' Hst
  subst Hst'
  simp only [inv_st]
  rw [inv_frac_0]
  icases HP with ⟨Hrauth, Htoks, >Hl, HP⟩
  imod Hmask with _
  imod Hclose $$ [Hst Hrauth] with _
  · inext
    iexists rwmutex.Locked
    iframe Hst
    simp only [inv_st]
    iexact Hrauth
  imodintro
  iapply HΦ
  simp only [own_RWMutex_Locked_unseal, own_RWMutex_Locked_def]
  iframe HP
  iexists γ, γmax, γrlocked, γlocked
  iframe Hl Hown Hmax
  iframe #

theorem wp_RWMutex__Unlock (rw : loc) (P : Qp → IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ own_RWMutex_Locked rw P ∗ ▷ P 1 }}
      (App (Val (rw @!! go.type.PointerType RWMutex @!! go!"Unlock")) (Val #()))
    {{ RET #(); own_RWMutex rw P }} := by
  wp_start_folded as ⟨Ho, HP_in⟩
  simp only [own_RWMutex_Locked_unseal, own_RWMutex_Locked_def]
  icases Ho with ⟨%γ, %γmax, %γrlocked, %γlocked, Ho⟩
  iNamed Ho
  wp_apply_core rwmutex.wp_RWMutex__Unlock γ rw (nroot.@"rw") $$ [] [-]
  · iframe #
  iinv Hinv with Hi Hclose <;> try exact ⟨mask_ndot_ne nroot "inv" "rw" (by decide), trivial⟩
  icases Hi with ⟨%st, >Hst, HP⟩
  cases st with
  | RLocked n =>
    simp only [inv_st]
    icases HP with ⟨_, _, >Hbad, _⟩
    icombine Hlocked Hbad gives % ⟨Hbad, _⟩
    exfalso
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
    grind
  | Locked =>
  simp only [inv_st]
  iframe Hst
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iintro Hst
  imod own_toks_0 γmax with H0
  imod Hmask with _
  imod Hclose $$ [Hst HP Hlocked HP_in H0] with _
  · inext
    iexists (rwmutex.RLocked 0)
    iframe Hst
    simp only [inv_st]
    rw [inv_frac_0]
    iframe
  imodintro
  iapply HΦ
  simp only [own_RWMutex_unseal, own_RWMutex_def]
  iexists γ, γmax, γrlocked, γlocked
  iframe Hown_rlock Hmax
  iframe #

theorem replicate_helper (R Q : IProp GF) (γ : GName) (n : Nat) :
    □ (R -∗ own_toks γ 1 -∗ Q) ∗ own_toks γ n ∗ ([∗list] _x ∈ List.replicate n (), R) ⊢
      [∗list] _x ∈ List.replicate n (), Q := by
  induction n with
  | zero =>
    simp only [List.replicate]
    exact BigSepL.bigSepL_nil_intro
  | succ n ih =>
    iintro ⟨#Hmk, Htoks, Hrs⟩
    simp only [List.replicate]
    iapply BigSepL.bigSepL_cons.2
    icases (own_toks_add 1 n γ).1 $$ Htoks with ⟨Htoks, Htok⟩
    icases BigSepL.bigSepL_cons.1 $$ Hrs with ⟨Hr, Hrs⟩
    isplitl [Hr Htok]
    · iapply Hmk $$ Hr Htok
    · iapply ih $$ [$Hmk $Htoks $Hrs]

theorem init_RWMutex (P : Qp → IProp GF) {E : CoPset} (rw : loc) [HPfrac : Fractional P] :
    ⊢ ▷ P 1 -∗ typed_pointsto (GF := GF) rw (zero_val RWMutex.t) (DFrac.own 1) ={E}=∗
      [∗list] _x ∈ List.replicate (Int.toNat rwmutex.actualMaxReaders) (), own_RWMutex rw P := by
  iintro HP Hrw
  imod rwmutex.init_RWMutex (E := E) (nroot.@"rw") rw $$ Hrw with ⟨%γ, #His, Hstate, Hrtoks⟩
  imod own_tok_auth_alloc (GF := GF) with ⟨%γmax, Hauth⟩
  imod own_tok_auth_add (Int.toNat rwmutex.actualMaxReaders) γmax 0 $$ Hauth with ⟨Hauth, Htoks⟩
  simp only [Nat.zero_add]
  imod (update_into_persistently (P := own_tok_auth_dfrac (GF := GF) γmax (DFrac.own 1) _)) $$ Hauth
    with #Hauth
  imod own_tok_auth_alloc (GF := GF) with ⟨%γrlocked, Hrauth⟩
  imod ghost_var_alloc () with ⟨%γlocked, Hl⟩
  imod own_toks_0 (GF := GF) γmax with H0
  imod inv_alloc (nroot.@"inv") E
    iprop(∃ st, rwmutex.own_RWMutex γ st ∗ inv_st P γrlocked γmax γlocked st) $$ [Hstate Hrauth Hl H0 HP]
    with #Hinv
  · inext
    iexists (rwmutex.RLocked 0)
    iframe Hstate
    simp only [inv_st]
    rw [inv_frac_0]
    iframe
  imodintro
  ihave #HPf : (□ (∀ q1 q2, P (q1 + q2) ∗-∗ P q1 ∗ P q2) : IProp GF) $$ []
  · imodintro
    iintro %q1 %q2
    isplit
    · iintro H; iapply (HPfrac.fractional q1 q2).1 $$ H
    · iintro H; iapply (HPfrac.fractional q1 q2).2 $$ H
  ihave #Hmk : (□ (rwmutex.own_RLock_token γ -∗ own_toks γmax 1 -∗ own_RWMutex rw P) : IProp GF) $$ []
  · imodintro
    iintro Hrtok Htok
    simp only [own_RWMutex_unseal, own_RWMutex_def]
    iexists γ, γmax, γrlocked, γlocked
    iframe Hrtok Htok
    iframe #
  iapply replicate_helper $$ [$Hmk $Htoks $Hrtoks]

end wps

end sync

end Perennial
end
