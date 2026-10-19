/-
A spin lock on a Boolean, the basis of
`primitive.Mutex` and `sync.Mutex`.

* `is_lock m R`: `m` is a lock protecting `R` (persistent);
* `ownLock m`: the lock is held.

The lock invariant owns `1/4` of `m ↦ b` and, when the lock is free, the other
`3/4` and `R`; `ownLock m` is the `3/4` of `m ↦ true`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Defn.Lock
public import Perennial.Golang.Theory.Pre
public import Perennial.Proof.TokSet

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics]



/-- Splitting a full typed points-to into `1/4` and `3/4`. -/
theorem typedPointsto_quarter_three_quarter {V : Type} [TypedPointsto (GF := GF) V]
    (l : Loc) (v : V) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊣⊢ (l ↦{DFrac.own Qp.quarter} v ∗ l ↦{DFrac.own Qp.threeQuarters} v) := by
  have h : (DFrac.own 1 : DFrac) = DFrac.own Qp.quarter • DFrac.own Qp.threeQuarters := by
    rw [DFrac.op_own, Qp.quarter_add_threeQuarters]
  rw [h]
  exact (typedPointsto_dfractional (GF := GF) l v).dfractional _ _

/-- The lock invariant. -/
abbrev lockInv (m : Loc) (R : IProp GF) : IProp GF :=
  iprop(∃ b : Bool, m ↦{DFrac.own Qp.quarter} b ∗
      (if b then iprop(True) else iprop(m ↦{DFrac.own Qp.threeQuarters} b ∗ R)))

def isLockDef (m : Loc) (R : IProp GF) : IProp GF :=
  iprop("#Hinv" ∷ inv nroot (lockInv m R) ∗
    "_" ∷ True)
/-- This means `m` is a valid lock with invariant `R` (sealed). -/
@[irreducible] def isLock (m : Loc) (R : IProp GF) : IProp GF := isLockDef m R
theorem isLock_unseal : @isLock = @isLockDef := by funext; with_unfolding_all rfl

def ownLockDef (m : Loc) : IProp GF := typedPointsto (GF := GF) m true (DFrac.own Qp.threeQuarters)
/-- This resource denotes ownership of the fact that the lock is currently
locked (sealed). -/
@[irreducible] def ownLock (m : Loc) : IProp GF := ownLockDef m
theorem ownLock_unseal : @ownLock = @ownLockDef := by funext; with_unfolding_all rfl

theorem ownLock_exclusive (m : Loc) : ⊢ ownLock (GF := GF) m -∗ ownLock m -∗ False := by
  rw [ownLock_unseal]; unfold ownLockDef
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  iintro ⟨H1, _⟩ ⟨H2, _⟩
  simp only [typedPointsto_bool, typedPointstoDef_heap]
  icombine H1 H2 gives % ⟨Hbad, _⟩
  exfalso
  have : (3 / 4 + 3 / 4 : Rat) ≤ 1 := Hbad
  grind

instance isLock_ne (m : Loc) : NonExpansive (isLock (GF := GF) m) where
  ne n R1 R2 h := by
    rw [isLock_unseal]; unfold isLockDef named
    refine BI.sep_ne.ne ((inv_ne nroot).ne ?_) .rfl
    unfold lockInv
    refine exists_ne fun b => BI.sep_ne.ne .rfl ?_
    cases b
    · exact BI.sep_ne.ne .rfl h
    · exact .rfl

instance isLock_persistent (m : Loc) (R : IProp GF) : Persistent (isLock m R) := by
  rw [isLock_unseal]; unfold isLockDef named; infer_instance

instance locked_timeless (m : Loc) : Timeless (ownLock (GF := GF) m) := by
  rw [ownLock_unseal]; unfold ownLockDef; infer_instance

theorem init_lock (R : IProp GF) (E : CoPset) (m : Loc) :
    ⊢ typedPointsto (GF := GF) m false (DFrac.own 1) -∗ ▷ R ={E}=∗ isLock m R := by
  iintro Hl HR
  rw [isLock_unseal]; unfold isLockDef
  icases (typedPointsto_quarter_three_quarter m false).1 $$ Hl with ⟨Hl1, Hl2⟩
  imod inv_alloc nroot E (lockInv m R) $$ [Hl1 Hl2 HR] with #Hinv
  · inext
    unfold lockInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
  imodintro
  iframe Hinv

theorem wp_lock_trylock (m : Loc) (R : IProp GF) :
    {{ isLock m R }} (App (Val lock.trylock) (Val #m))
    {{ (locked : Bool), RET #locked; if locked then ownLock m ∗ R else True }} := by
  wp_start_folded as H
  unfold lock.trylock
  wp_call
  simp only [isLock_unseal, isLockDef]
  iNamed H
  wp_bind (CmpXchg _ _ _)
  iinv Hinv with ⟨%b, Hl, HR⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases HR with ⟨>Hl2, HR⟩
    icases Hl with >Hl
    ihave Hfull := (typedPointsto_quarter_three_quarter m false).2 $$ [Hl Hl2]
    · iframe
    wp_apply_core wp_cmpxchg_suc m false false true _ _ rfl $$ Hfull
    iintro Hl
    icases (typedPointsto_quarter_three_quarter m true).1 $$ Hl with ⟨Hl1, Hl2⟩
    imodintro
    isplitl [Hl1]
    · inext; iexists true; simp only [↓reduceIte]; iframe
    wp_pures
    iapply HΦ
    simp only [↓reduceIte, ownLock_unseal, ownLockDef]
    iframe
  · simp only [↓reduceIte]
    wp_apply_core wp_cmpxchg_fail m true false true (DFrac.own Qp.quarter) _ _ (by decide) $$ Hl
    iintro Hl
    imodintro
    isplitl [Hl]
    · inext; iexists true; simp only [↓reduceIte]; iframe
    wp_pures
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial

theorem wp_lock_lock (m : Loc) (R : IProp GF) :
    {{ isLock m R }} (App (Val lock.lock) (Val #m)) {{ RET #(); ownLock m ∗ R }} := by
  unfold lock.lock
  iloeb as IH
  wp_start_folded as H
  wp_call
  simp only [isLock_unseal, isLockDef]
  iNamed H
  wp_bind (CmpXchg _ _ _)
  iinv Hinv with ⟨%b, Hl, HR⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases HR with ⟨>Hl2, HR⟩
    icases Hl with >Hl
    ihave Hfull := (typedPointsto_quarter_three_quarter m false).2 $$ [Hl Hl2]
    · iframe
    wp_apply_core wp_cmpxchg_suc m false false true _ _ rfl $$ Hfull
    iintro Hl
    icases (typedPointsto_quarter_three_quarter m true).1 $$ Hl with ⟨Hl1, Hl2⟩
    imodintro
    isplitl [Hl1]
    · inext; iexists true; simp only [↓reduceIte]; iframe
    wp_pures
    iapply HΦ
    simp only [ownLock_unseal, ownLockDef]
    iframe
  · simp only [↓reduceIte]
    wp_apply_core wp_cmpxchg_fail m true false true (DFrac.own Qp.quarter) _ _ (by decide) $$ Hl
    iintro Hl
    imodintro
    isplitl [Hl]
    · inext; iexists true; simp only [↓reduceIte]; iframe
    wp_pure
    wp_pure
    iapply IH $$ [] HΦ
    iframe Hinv

theorem wp_lock_unlock (m : Loc) (R : IProp GF) :
    {{ isLock m R ∗ ownLock m ∗ ▷ R }} (App (Val lock.unlock) (Val #m)) {{ RET #(); True }} := by
  wp_start_folded as ⟨#His, Hlocked, HR⟩
  unfold lock.unlock
  wp_call
  simp only [isLock_unseal, isLockDef, ownLock_unseal, ownLockDef]
  iNamed His
  wp_bind (CmpXchg _ _ _)
  iinv Hinv with ⟨%b, >Hl, _⟩
  icombine Hl Hlocked gives %Heq
  subst Heq
  ihave Hfull := (typedPointsto_quarter_three_quarter m true).2 $$ [Hl Hlocked]
  · iframe
  wp_apply_core wp_cmpxchg_suc m true true false _ _ rfl $$ Hfull
  iintro Hl
  icases (typedPointsto_quarter_three_quarter m false).1 $$ Hl with ⟨Hl1, Hl2⟩
  imodintro
  isplitl [Hl1 Hl2 HR]
  · inext; iexists false; simp only [Bool.false_eq_true, ↓reduceIte]; iframe
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
end
