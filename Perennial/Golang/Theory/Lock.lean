/-
Port of `new/golang/theory/lock.v`: a spin lock on a Boolean, the basis of
`primitive.Mutex` and `sync.Mutex`.

* `is_lock m R`: `m` is a lock protecting `R` (persistent);
* `own_lock m`: the lock is held.

The lock invariant owns `1/4` of `m ↦ b` and, when the lock is free, the other
`3/4` and `R`; `own_lock m` is the `3/4` of `m ↦ true`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Golang.Defn.Lock
import Perennial.Golang.Theory.Pre
import Perennial.Proof.TokSet
import Perennial.Experiments.Glob

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics]



/-- Splitting a full typed points-to into `1/4` and `3/4` (Rocq
`Qp.quarter_three_quarter`). -/
theorem typed_pointsto_quarter_three_quarter {V : Type} [TypedPointsto (GF := GF) V]
    (l : loc) (v : V) :
    typed_pointsto (GF := GF) l v (DFrac.own 1) ⊣⊢ (l ↦{DFrac.own Qp.quarter} v ∗ l ↦{DFrac.own Qp.threeQuarters} v) := by
  have h : (DFrac.own 1 : DFrac) = DFrac.own Qp.quarter • DFrac.own Qp.threeQuarters := by
    rw [DFrac.op_own, Qp.quarter_add_threeQuarters]
  rw [h]
  exact (typed_pointsto_dfractional (GF := GF) l v).dfractional _ _

/-- The lock invariant. -/
abbrev lock_inv (m : loc) (R : IProp GF) : IProp GF :=
  iprop(∃ b : Bool, m ↦{DFrac.own Qp.quarter} b ∗
      (if b then iprop(True) else iprop(m ↦{DFrac.own Qp.threeQuarters} b ∗ R)))

def is_lock_def (m : loc) (R : IProp GF) : IProp GF :=
  iprop("#Hinv" ∷ inv nroot (lock_inv m R) ∗
    "_" ∷ True)
/-- This means `m` is a valid lock with invariant `R` (Rocq `Opaque is_lock`). -/
@[irreducible] def is_lock (m : loc) (R : IProp GF) : IProp GF := is_lock_def m R
theorem is_lock_unseal : @is_lock = @is_lock_def := by funext; with_unfolding_all rfl

def own_lock_def (m : loc) : IProp GF := typed_pointsto (GF := GF) m true (DFrac.own Qp.threeQuarters)
/-- This resource denotes ownership of the fact that the lock is currently
locked (Rocq `Opaque own_lock`). -/
@[irreducible] def own_lock (m : loc) : IProp GF := own_lock_def m
theorem own_lock_unseal : @own_lock = @own_lock_def := by funext; with_unfolding_all rfl

theorem own_lock_exclusive (m : loc) : ⊢ own_lock (GF := GF) m -∗ own_lock m -∗ False := by
  rw [own_lock_unseal]; unfold own_lock_def
  rw [typed_pointsto_unseal]; unfold typed_pointsto_wrap
  iintro ⟨H1, _⟩ ⟨H2, _⟩
  simp only [typed_pointsto_bool, typed_pointsto_def_heap]
  icombine H1 H2 gives % ⟨Hbad, _⟩
  exfalso
  have : (3 / 4 + 3 / 4 : Rat) ≤ 1 := Hbad
  grind

instance is_lock_ne (m : loc) : NonExpansive (is_lock (GF := GF) m) where
  ne n R1 R2 h := by
    rw [is_lock_unseal]; unfold is_lock_def named
    refine BI.sep_ne.ne ((inv_ne nroot).ne ?_) .rfl
    unfold lock_inv
    refine exists_ne fun b => BI.sep_ne.ne .rfl ?_
    cases b
    · exact BI.sep_ne.ne .rfl h
    · exact .rfl

instance is_lock_persistent (m : loc) (R : IProp GF) : Persistent (is_lock m R) := by
  rw [is_lock_unseal]; unfold is_lock_def named; infer_instance

instance locked_timeless (m : loc) : Timeless (own_lock (GF := GF) m) := by
  rw [own_lock_unseal]; unfold own_lock_def; infer_instance

theorem init_lock (R : IProp GF) (E : CoPset) (m : loc) :
    ⊢ typed_pointsto (GF := GF) m false (DFrac.own 1) -∗ ▷ R ={E}=∗ is_lock m R := by
  iintro Hl HR
  rw [is_lock_unseal]; unfold is_lock_def
  icases (typed_pointsto_quarter_three_quarter m false).1 $$ Hl with ⟨Hl1, Hl2⟩
  imod inv_alloc nroot E (lock_inv m R) $$ [Hl1 Hl2 HR] with #Hinv
  · inext
    unfold lock_inv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
  imodintro
  iframe Hinv

theorem wp_lock_trylock (m : loc) (R : IProp GF) :
    {{ is_lock m R }} (App (Val lock.trylock) (Val #m))
    {{ (locked : Bool), RET #locked; if locked then own_lock m ∗ R else True }} := by
  wp_start_folded as H
  unfold lock.trylock
  wp_call
  simp only [is_lock_unseal, is_lock_def]
  iNamed H
  wp_bind (CmpXchg _ _ _)
  iinv Hinv with ⟨%b, Hl, HR⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases HR with ⟨>Hl2, HR⟩
    icases Hl with >Hl
    ihave Hfull := (typed_pointsto_quarter_three_quarter m false).2 $$ [Hl Hl2]
    · iframe
    wp_apply_core wp_cmpxchg_suc m false false true _ _ rfl $$ Hfull
    iintro Hl
    icases (typed_pointsto_quarter_three_quarter m true).1 $$ Hl with ⟨Hl1, Hl2⟩
    imodintro
    isplitl [Hl1]
    · inext; iexists true; simp only [↓reduceIte]; iframe
    wp_pures
    iapply HΦ
    simp only [↓reduceIte, own_lock_unseal, own_lock_def]
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

theorem wp_lock_lock (m : loc) (R : IProp GF) :
    {{ is_lock m R }} (App (Val lock.lock) (Val #m)) {{ RET #(); own_lock m ∗ R }} := by
  unfold lock.lock
  iloeb as IH
  wp_start_folded as H
  wp_call
  simp only [is_lock_unseal, is_lock_def]
  iNamed H
  wp_bind (CmpXchg _ _ _)
  iinv Hinv with ⟨%b, Hl, HR⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases HR with ⟨>Hl2, HR⟩
    icases Hl with >Hl
    ihave Hfull := (typed_pointsto_quarter_three_quarter m false).2 $$ [Hl Hl2]
    · iframe
    wp_apply_core wp_cmpxchg_suc m false false true _ _ rfl $$ Hfull
    iintro Hl
    icases (typed_pointsto_quarter_three_quarter m true).1 $$ Hl with ⟨Hl1, Hl2⟩
    imodintro
    isplitl [Hl1]
    · inext; iexists true; simp only [↓reduceIte]; iframe
    wp_pures
    iapply HΦ
    simp only [own_lock_unseal, own_lock_def]
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

theorem wp_lock_unlock (m : loc) (R : IProp GF) :
    {{ is_lock m R ∗ own_lock m ∗ ▷ R }} (App (Val lock.unlock) (Val #m)) {{ RET #(); True }} := by
  wp_start_folded as ⟨#His, Hlocked, HR⟩
  unfold lock.unlock
  wp_call
  simp only [is_lock_unseal, is_lock_def, own_lock_unseal, own_lock_def]
  iNamed His
  wp_bind (CmpXchg _ _ _)
  iinv Hinv with ⟨%b, >Hl, _⟩
  icombine Hl Hlocked gives %Heq
  subst Heq
  ihave Hfull := (typed_pointsto_quarter_three_quarter m true).2 $$ [Hl Hlocked]
  · iframe
  wp_apply_core wp_cmpxchg_suc m true true false _ _ rfl $$ Hfull
  iintro Hl
  icases (typed_pointsto_quarter_three_quarter m false).1 $$ Hl with ⟨Hl1, Hl2⟩
  imodintro
  isplitl [Hl1 Hl2 HR]
  · inext; iexists false; simp only [Bool.false_eq_true, ↓reduceIte]; iframe
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
end
