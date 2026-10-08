/-
A specification for `RWMutex`
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

/-- `z` as a positive rational (`1` if `z ≤ 0`). -/
def posToQpZ (z : Int) : Qp := ⟨if 0 < z then (z : Rat) else 1, by
  split
  · exact Rat.intCast_pos.mpr ‹_›
  · decide⟩

theorem posToQpZ_val (z : Int) (h : 0 < z) : (posToQpZ z).val = (z : Rat) := by
  simp [posToQpZ, h]

def rfracDef : Qp := (1 : Qp) / posToQpZ (rwmutex.actualMaxReaders + 1)
@[irreducible] def rfrac : Qp := rfracDef
theorem rfrac_unseal : rfrac = rfracDef := by with_unfolding_all rfl

theorem actualMaxReaders_pos : 0 < rwmutex.actualMaxReaders := by
  rw [rwmutex.actualMaxReaders_unseal]; decide

/-- The fraction of `P` held by the invariant when there are `n` readers. -/
abbrev invFrac (n : Nat) : Qp :=
  QpMul (posToQpZ (rwmutex.actualMaxReaders + 1 - (n : Int))) rfrac

theorem invFrac_val (n : Nat) (h : (n : Int) ≤ rwmutex.actualMaxReaders) :
    (invFrac n).val =
      ((rwmutex.actualMaxReaders + 1 - (n : Int) : Int) : Rat) /
        ((rwmutex.actualMaxReaders + 1 : Int) : Rat) := by
  simp only [invFrac, QpMul, rfrac_unseal, rfracDef, Qp.val_div, Qp.val_one]
  rw [posToQpZ_val _ (by omega), posToQpZ_val _ (by have := actualMaxReaders_pos; omega)]
  rw [Rat.div_def, Rat.one_mul, Rat.div_def]

theorem invFrac_S (n : Nat) (h : ((n + 1 : Nat) : Int) ≤ rwmutex.actualMaxReaders) :
    invFrac n = rfrac + invFrac (n + 1) := by
  rw [Qp.ext_iff, Qp.val_add, invFrac_val n (by omega), invFrac_val (n + 1) h]
  simp only [rfrac_unseal, rfracDef, Qp.val_div, Qp.val_one]
  rw [posToQpZ_val _ (by have := actualMaxReaders_pos; omega)]
  rw [Rat.div_def, Rat.div_def, Rat.div_def, ← Rat.add_mul]
  congr 1
  push_cast
  grind

theorem invFrac_0 : invFrac 0 = 1 := by
  rw [Qp.ext_iff, invFrac_val 0 (by have := actualMaxReaders_pos; omega)]
  rw [show rwmutex.actualMaxReaders + 1 - ((0 : Nat) : Int) = rwmutex.actualMaxReaders + 1 by omega,
    Qp.val_one, Rat.div_def, Rat.mul_inv_cancel]
  have := actualMaxReaders_pos
  exact_mod_cast (show rwmutex.actualMaxReaders + 1 ≠ 0 by omega)

theorem mask_ndot_ne (N : Namespace) (x y : String) (h : x ≠ y) :
    (↑(N.@x) : CoPset) ⊆ ⊤ \ ↑(N.@y) := by
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint N h p ⟨hp, h'⟩⟩

/-- Needed for destructing `▷ ∃ st, ...`. -/
instance : Inhabited rwmutex := ⟨.Locked⟩

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

namespace rwmutex_guard

/-- The part of the invariant that depends on the `rwmutex` state. -/
def invSt (P : Qp → IProp GF) (γrlocked γmax γlocked : GName) : rwmutex → IProp GF
  | .Locked => ownTokAuth γrlocked 0
  | .RLocked n => iprop(ownTokAuth γrlocked n ∗ ownToks γmax n ∗
      ghostVar γlocked 1 () ∗ P (invFrac n))

/-- The lock invariant. -/
abbrev isInv (P : Qp → IProp GF) (γ : rwmutex.RWMutexNames) (γmax γrlocked γlocked : GName) :
    IProp GF :=
  inv (nroot.@"inv")
    iprop(∃ st, rwmutex.ownRWMutex γ st ∗ invSt P γrlocked γmax γlocked st)

end rwmutex_guard

open rwmutex_guard in
def ownRWMutexDef (rw : Loc) (P : Qp → IProp GF) : IProp GF :=
  iprop(∃ (γ : rwmutex.RWMutexNames) (γmax γrlocked γlocked : GName),
    "Hown" ∷ rwmutex.ownRLockToken γ ∗
    "Hmax" ∷ ownToks γmax 1 ∗
    "#His" ∷ rwmutex.isRWMutex rw γ (nroot.@"rw") ∗
    "#HPfrac" ∷ □ (∀ q1 q2, P (q1 + q2) ∗-∗ P q1 ∗ P q2) ∗
    "#Hauth" ∷ ownTokAuthDfrac γmax DFrac.discard (Int.toNat rwmutex.actualMaxReaders) ∗
    "#Hinv" ∷ isInv P γ γmax γrlocked γlocked)
@[irreducible] def ownRWMutex (rw : Loc) (P : Qp → IProp GF) : IProp GF := ownRWMutexDef rw P
theorem ownRWMutex_unseal : @ownRWMutex = @ownRWMutexDef := by funext; with_unfolding_all rfl

open rwmutex_guard in
def ownRWMutexRLockedDef (rw : Loc) (P : Qp → IProp GF) : IProp GF :=
  iprop(∃ (γ : rwmutex.RWMutexNames) (γmax γrlocked γlocked : GName),
    "Hrlocked" ∷ ownToks γrlocked 1 ∗
    "#His" ∷ rwmutex.isRWMutex rw γ (nroot.@"rw") ∗
    "#HPfrac" ∷ □ (∀ q1 q2, P (q1 + q2) ∗-∗ P q1 ∗ P q2) ∗
    "#Hauth" ∷ ownTokAuthDfrac γmax DFrac.discard (Int.toNat rwmutex.actualMaxReaders) ∗
    "#Hinv" ∷ isInv P γ γmax γrlocked γlocked)
@[irreducible] def ownRWMutexRLocked (rw : Loc) (P : Qp → IProp GF) : IProp GF :=
  ownRWMutexRLockedDef rw P
theorem ownRWMutexRLocked_unseal : @ownRWMutexRLocked = @ownRWMutexRLockedDef := by
  funext; with_unfolding_all rfl

open rwmutex_guard in
def ownRWMutexLockedDef (rw : Loc) (P : Qp → IProp GF) : IProp GF :=
  iprop(∃ (γ : rwmutex.RWMutexNames) (γmax γrlocked γlocked : GName),
    "Hlocked" ∷ ghostVar γlocked 1 () ∗
    "Hown_rlock" ∷ rwmutex.ownRLockToken γ ∗
    "Hmax" ∷ ownToks γmax 1 ∗
    "#His" ∷ rwmutex.isRWMutex rw γ (nroot.@"rw") ∗
    "#HPfrac" ∷ □ (∀ q1 q2, P (q1 + q2) ∗-∗ P q1 ∗ P q2) ∗
    "#Hauth" ∷ ownTokAuthDfrac γmax DFrac.discard (Int.toNat rwmutex.actualMaxReaders) ∗
    "#Hinv" ∷ isInv P γ γmax γrlocked γlocked)
@[irreducible] def ownRWMutexLocked (rw : Loc) (P : Qp → IProp GF) : IProp GF :=
  ownRWMutexLockedDef rw P
theorem ownRWMutexLocked_unseal : @ownRWMutexLocked = @ownRWMutexLockedDef := by
  funext; with_unfolding_all rfl

open rwmutex_guard

theorem RWMutex.wp_RLock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutex rw P }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"RLock")) (Val #()))
    {{ RET #(); ownRWMutexRLocked rw P ∗ ▷ P rfrac }} := by
  wp_start_folded as Hpre
  simp only [ownRWMutex_unseal, ownRWMutexDef]
  icases Hpre with ⟨%γ, %γmax, %γrlocked, %γlocked, Hpre⟩
  iNamed Hpre
  wp_apply_core rwmutex.RWMutex.wp_RLock γ rw (nroot.@"rw") $$ [Hown] [-]
  · iframe #; iframe
  iinv Hinv with Hi Hclose <;> try exact ⟨mask_ndot_ne nroot "inv" "rw" (by decide), trivial⟩
  icases Hi with ⟨%st, >Hst, HP⟩
  iframe Hst
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iintro %n %Hst' H
  subst Hst'
  simp only [invSt]
  icases HP with ⟨>Hrtok, >Htoks, Hl, HP⟩
  icombine Htoks Hmax as Htoks
  icombine Hauth Htoks gives %Hle
  rw [invFrac_S n (by omega)]
  imod ownTokAuth_add 1 γrlocked n $$ Hrtok with ⟨Hrtok, Ht⟩
  icases HPfrac $$ HP with ⟨HP', HP⟩
  imod Hmask with _
  imod Hclose $$ [Hrtok Htoks Hl HP H] with _
  · inext
    iexists (rwmutex.RLocked (n + 1))
    iframe H
    simp only [invSt]
    iframe
  imodintro
  iapply HΦ
  simp only [ownRWMutexRLocked_unseal, ownRWMutexRLockedDef]
  iframe HP'
  iexists γ, γmax, γrlocked, γlocked
  iframe Ht
  iframe #

theorem RWMutex.wp_RUnlock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutexRLocked rw P ∗ ▷ P rfrac }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"RUnlock")) (Val #()))
    {{ RET #(); ownRWMutex rw P }} := by
  wp_start_folded as ⟨Ho, HP_in⟩
  simp only [ownRWMutexRLocked_unseal, ownRWMutexRLockedDef]
  icases Ho with ⟨%γ, %γmax, %γrlocked, %γlocked, Ho⟩
  iNamed Ho
  wp_apply_core rwmutex.RWMutex.wp_RUnlock γ rw (nroot.@"rw") $$ [] [-]
  · iframe #
  iinv Hinv with Hi Hclose <;> try exact ⟨mask_ndot_ne nroot "inv" "rw" (by decide), trivial⟩
  icases Hi with ⟨%st, >Hst, HP⟩
  cases st with
  | Locked =>
    simp only [invSt]
    icases HP with >HP
    icombine HP Hrlocked gives %Hbad
    omega
  | RLocked n =>
  simp only [invSt]
  icases HP with ⟨>Hrauth, >Htoks, Hl, HP⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  icombine Hrauth Hrlocked gives %Hle
  icombine Hauth Htoks gives %Hmaxle
  iexists (n - 1)
  rw [show n - 1 + 1 = n by omega]
  iframe Hst
  iintro ⟨Hst, Hrlock⟩
  imod ownTokAuth_sub 1 γrlocked n $$ Hrauth Hrlocked with Hrauth
  icases ownToks_add_1 1 (n - 1) γmax $$ [Htoks] with ⟨Htoks, Htok⟩
  · rw [show n - 1 + 1 = n by omega]; iexact Htoks
  imod Hmask with _
  imod Hclose $$ [Hst Hrauth Htoks Hl HP HP_in] with _
  · inext
    iexists (rwmutex.RLocked (n - 1))
    iframe Hst
    simp only [invSt]
    iframe
    ihave HP := HPfrac $$ %rfrac %(invFrac n) [HP HP_in]
    · iframe
    rw [invFrac_S (n - 1) (by omega), show n - 1 + 1 = n by omega]
    iexact HP
  imodintro
  iapply HΦ
  simp only [ownRWMutex_unseal, ownRWMutexDef]
  iexists γ, γmax, γrlocked, γlocked
  iframe Hrlock Htok
  iframe #

theorem RWMutex.wp_Lock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutex rw P }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); ownRWMutexLocked rw P ∗ ▷ P 1 }} := by
  wp_start_folded as Ho
  simp only [ownRWMutex_unseal, ownRWMutexDef]
  icases Ho with ⟨%γ, %γmax, %γrlocked, %γlocked, Ho⟩
  iNamed Ho
  wp_apply_core rwmutex.RWMutex.wp_Lock γ rw (nroot.@"rw") $$ [] [-]
  · iframe #
  iinv Hinv with Hi Hclose <;> try exact ⟨mask_ndot_ne nroot "inv" "rw" (by decide), trivial⟩
  icases Hi with ⟨%st, >Hst, HP⟩
  iframe Hst
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iintro %Hst' Hst
  subst Hst'
  simp only [invSt]
  rw [invFrac_0]
  icases HP with ⟨Hrauth, Htoks, >Hl, HP⟩
  imod Hmask with _
  imod Hclose $$ [Hst Hrauth] with _
  · inext
    iexists rwmutex.Locked
    iframe Hst
    simp only [invSt]
    iexact Hrauth
  imodintro
  iapply HΦ
  simp only [ownRWMutexLocked_unseal, ownRWMutexLockedDef]
  iframe HP
  iexists γ, γmax, γrlocked, γlocked
  iframe Hl Hown Hmax
  iframe #

theorem RWMutex.wp_Unlock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutexLocked rw P ∗ ▷ P 1 }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); ownRWMutex rw P }} := by
  wp_start_folded as ⟨Ho, HP_in⟩
  simp only [ownRWMutexLocked_unseal, ownRWMutexLockedDef]
  icases Ho with ⟨%γ, %γmax, %γrlocked, %γlocked, Ho⟩
  iNamed Ho
  wp_apply_core rwmutex.RWMutex.wp_Unlock γ rw (nroot.@"rw") $$ [] [-]
  · iframe #
  iinv Hinv with Hi Hclose <;> try exact ⟨mask_ndot_ne nroot "inv" "rw" (by decide), trivial⟩
  icases Hi with ⟨%st, >Hst, HP⟩
  cases st with
  | RLocked n =>
    simp only [invSt]
    icases HP with ⟨_, _, >Hbad, _⟩
    icombine Hlocked Hbad gives % ⟨Hbad, _⟩
    exfalso
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
    grind
  | Locked =>
  simp only [invSt]
  iframe Hst
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iintro Hst
  imod ownToks_0 γmax with H0
  imod Hmask with _
  imod Hclose $$ [Hst HP Hlocked HP_in H0] with _
  · inext
    iexists (rwmutex.RLocked 0)
    iframe Hst
    simp only [invSt]
    rw [invFrac_0]
    iframe
  imodintro
  iapply HΦ
  simp only [ownRWMutex_unseal, ownRWMutexDef]
  iexists γ, γmax, γrlocked, γlocked
  iframe Hown_rlock Hmax
  iframe #

theorem replicate_helper (R Q : IProp GF) (γ : GName) (n : Nat) :
    □ (R -∗ ownToks γ 1 -∗ Q) ∗ ownToks γ n ∗ ([∗list] _x ∈ List.replicate n (), R) ⊢
      [∗list] _x ∈ List.replicate n (), Q := by
  induction n with
  | zero =>
    simp only [List.replicate]
    exact BigSepL.bigSepL_nil_intro
  | succ n ih =>
    iintro ⟨#Hmk, Htoks, Hrs⟩
    simp only [List.replicate]
    iapply BigSepL.bigSepL_cons.2
    icases (ownToks_add 1 n γ).1 $$ Htoks with ⟨Htoks, Htok⟩
    icases BigSepL.bigSepL_cons.1 $$ Hrs with ⟨Hr, Hrs⟩
    isplitl [Hr Htok]
    · iapply Hmk $$ Hr Htok
    · iapply ih $$ [$Hmk $Htoks $Hrs]

theorem init_RWMutex (P : Qp → IProp GF) {E : CoPset} (rw : Loc) [HPfrac : Fractional P] :
    ⊢ ▷ P 1 -∗ typedPointsto (GF := GF) rw (zero_val RWMutex) (DFrac.own 1) ={E}=∗
      [∗list] _x ∈ List.replicate (Int.toNat rwmutex.actualMaxReaders) (), ownRWMutex rw P := by
  iintro HP Hrw
  imod rwmutex.init_RWMutex (E := E) (nroot.@"rw") rw $$ Hrw with ⟨%γ, #His, Hstate, Hrtoks⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γmax, Hauth⟩
  imod ownTokAuth_add (Int.toNat rwmutex.actualMaxReaders) γmax 0 $$ Hauth with ⟨Hauth, Htoks⟩
  simp only [Nat.zero_add]
  imod (update_into_persistently (P := ownTokAuthDfrac (GF := GF) γmax (DFrac.own 1) _)) $$ Hauth
    with #Hauth
  imod ownTokAuth_alloc (GF := GF) with ⟨%γrlocked, Hrauth⟩
  imod ghostVar_alloc () with ⟨%γlocked, Hl⟩
  imod ownToks_0 (GF := GF) γmax with H0
  imod inv_alloc (nroot.@"inv") E
    iprop(∃ st, rwmutex.ownRWMutex γ st ∗ invSt P γrlocked γmax γlocked st) $$ [Hstate Hrauth Hl H0 HP]
    with #Hinv
  · inext
    iexists (rwmutex.RLocked 0)
    iframe Hstate
    simp only [invSt]
    rw [invFrac_0]
    iframe
  imodintro
  ihave #HPf : (□ (∀ q1 q2, P (q1 + q2) ∗-∗ P q1 ∗ P q2) : IProp GF) $$ []
  · imodintro
    iintro %q1 %q2
    isplit
    · iintro H; iapply (HPfrac.fractional q1 q2).1 $$ H
    · iintro H; iapply (HPfrac.fractional q1 q2).2 $$ H
  ihave #Hmk : (□ (rwmutex.ownRLockToken γ -∗ ownToks γmax 1 -∗ ownRWMutex rw P) : IProp GF) $$ []
  · imodintro
    iintro Hrtok Htok
    simp only [ownRWMutex_unseal, ownRWMutexDef]
    iexists γ, γmax, γrlocked, γlocked
    iframe Hrtok Htok
    iframe #
  iapply replicate_helper $$ [$Hmk $Htoks $Hrtoks]

end wps

end sync

end Perennial
end
