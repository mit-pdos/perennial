/-
Shared definitions of the proofs of `sync.Pool`: `isPool p f R P`, a pool at `p` whose `New` is
`f`, which may assume `R`, and whose values satisfy `P`, and its initialization `init_Pool`; and
the pool's state in the Go model of `Get` and `Put` (`goose/model/overlay/sync/pool.go`), a
`*poolModel` in the field `local`: `isPoolModel s P`, a `poolModel` at `s` whose elements all
satisfy `P`, and its initialization `init_poolModel`.
-/
module

public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

/-- `Get`'s removal of `xs[k]`: `xs[k]` overwritten with the last element, and the last
slot dropped, is a permutation of `xs` without `xs[k]`. -/
theorem swapRemove_perm {α : Type _} (xs : List α) (k : Nat) (hk : k < xs.length) :
    ((xs.set k (xs[xs.length - 1]'(by omega))).take (xs.length - 1) ++ [xs[k]]).Perm xs := by
  obtain ⟨ys, y, rfl⟩ : ∃ ys y, xs = ys ++ [y] := by
    rcases List.eq_nil_or_concat xs with h | h
    · subst h; simp at hk
    · obtain ⟨ys, y, h⟩ := h; exact ⟨ys, y, by simpa using h⟩
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hk ⊢
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.sub_self, List.getElem_singleton]
  rcases Nat.lt_or_ge k ys.length with h | h
  · rw [List.set_append_left _ _ h, List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp), List.getElem_append_left h,
      List.set_eq_take_append_cons_drop, ite_eq_left h]
    conv => rhs; lhs; rw [← List.take_append_drop k ys, List.drop_eq_getElem_cons h]
    simp only [List.append_assoc, List.cons_append]
    refine List.Perm.append_left _ ?_
    refine (List.Perm.cons _ (List.perm_append_singleton _ _)).trans ?_
    refine List.Perm.trans (List.Perm.swap _ _ _) ?_
    exact List.Perm.cons _ (List.perm_append_singleton _ _).symm
  · have : k = ys.length := by omega
    subst this
    simp

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The lock invariant of the pool state at `s`: its elements `xs`, each satisfying `P`. -/
def poolInv (s : Loc) (P : GoAny → IProp GF) : IProp GF :=
  iprop(∃ (sl : GoSlice) (xs : List GoAny),
    "items" ∷ s.[poolModel, go!"items"] ↦ sl ∗
    "Hsl" ∷ sl ↦* xs ∗
    "Hcap" ∷ ownSliceCap GoAny sl (DFrac.own 1) ∗
    "HP" ∷ [∗list] x ∈ xs, P x)

def isPoolModelDef (s : Loc) (P : GoAny → IProp GF) : IProp GF :=
  isMutex (s.[poolModel, go!"mu"]) (poolInv s P)
/-- `s` is a pool state (a `poolModel`) whose elements all satisfy `P` (sealed). -/
@[irreducible] def isPoolModel (s : Loc) (P : GoAny → IProp GF) : IProp GF :=
  isPoolModelDef s P
theorem isPoolModel_unseal : @isPoolModel = @isPoolModelDef := by
  funext; with_unfolding_all rfl

instance isPoolModel_persistent (s : Loc) (P : GoAny → IProp GF) :
    Persistent (isPoolModel s P) := by
  rw [isPoolModel_unseal]; unfold isPoolModelDef; infer_instance

/-- A zero `poolModel` (`new(poolModel)`) is an empty pool state. -/
theorem init_poolModel (s : Loc) (P : GoAny → IProp GF) (E : CoPset) :
    typedPointsto (GF := GF) s (zero_val poolModel) (DFrac.own 1) ⊢ |={E}=> isPoolModel s P := by
  iintro Hs
  rw [isPoolModel_unseal]; unfold isPoolModelDef
  iStructNamed Hs
  iapply init_Mutex (poolInv s P) E _ $$ mu
  inext
  unfold poolInv
  iexists slice.nil, []
  iframe items
  isplitl []
  · iapply ownSlice_nil
  isplitl []
  · iapply ownSliceCap_nil
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-- The invariant of the field `local` of the pool at `p`: `nil`, or a pool state whose
elements satisfy `P`. -/
def poolLocalInv (p : Loc) (P : GoAny → IProp GF) : IProp GF :=
  iprop(∃ (s : Loc),
    "Hlocal" ∷ p.[Pool, go!"local"] ↦ s ∗
    "Hs" ∷ (⌜s = null⌝ ∨ isPoolModel s P))

/-- `New` is `nil` or, given `R` (which it gives back), returns values satisfying `P`. `R` is
what a caller of `Get` holds and lends to `New` for the call: `True` when `New` needs nothing; a
resource when `New` reads state that is only valid while its holder is (a closure over a
variable its creator writes again later, valid only for as long as the creator's protocol
says). -/
def newSpec (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF) : IProp GF :=
  iprop(⌜f = func.nil⌝ ∨ {{ R }} (App (Val #f) (Val #())) {{ (x : GoAny), RET #x; P x ∗ R }})

instance newSpec_persistent (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF) :
    Persistent (newSpec f R P) := by
  unfold newSpec; infer_instance

/-- A `New` that needs nothing (a triple with precondition `True`) has a `newSpec` for any `R`. -/
theorem newSpec_of_true (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF) :
    iprop(⌜f = func.nil⌝ ∨ {{ True }} (App (Val #f) (Val #())) {{ (x : GoAny), RET #x; P x }}) ⊢
      newSpec f R P := by
  unfold newSpec
  iintro (%h | #H)
  · ileft; ipureintro; exact h
  iright
  wp_start as HR
  wp_apply H as %x Hx
  iapply HΦ
  iframe

def isPoolDef (p : Loc) (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF) : IProp GF :=
  iprop("#New" ∷ p.[Pool, go!"New"] ↦□ f ∗
    "#HNew" ∷ newSpec f R P ∗
    "#Hinv" ∷ inv nroot (poolLocalInv p P))
/-- `p` is a `sync.Pool` whose field `New` is `f` (no longer written), which `Get` calls lending
it the caller's `R`, and whose values (those `Put` and those `New` returns) satisfy `P`
(sealed). -/
@[irreducible] def isPool (p : Loc) (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF) :
    IProp GF :=
  isPoolDef p f R P
theorem isPool_unseal : @isPool = @isPoolDef := by funext; with_unfolding_all rfl

instance isPool_persistent (p : Loc) (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF) :
    Persistent (isPool p f R P) := by
  rw [isPool_unseal]; unfold isPoolDef named; infer_instance

/-- A pool's `isPool` holds for any other `New` spec `R'` that its `New` meets: `isPool` is the
field `New`, its spec and the pool's invariant, which does not mention the spec. (A pool
initialized once serves several `R`s: `init_Pool` at one, this lemma for the others.) -/
theorem isPool_respec (p : Loc) (f : GoFunc) (R R' : IProp GF) (P : GoAny → IProp GF) :
    isPool p f R P ∗ newSpec f R' P ⊢ isPool p f R' P := by
  rw [isPool_unseal]
  unfold isPoolDef named
  iintro ⟨⟨#HN, -, #Hinv⟩, #Hs⟩
  iframe #

/-- A pool not used yet (its field `local` is `nil`, as in the zero `Pool` and in
`Pool{New: f}`) becomes an `isPool`, with its `New`. The pool's points-to can be kept until
`New`'s spec is known (no method has been called while its owner holds it). -/
theorem init_Pool (p : Loc) (v : Pool) (R : IProp GF) (P : GoAny → IProp GF) (E : CoPset)
    (hlocal : v.local' = null) :
    typedPointsto (GF := GF) p v (DFrac.own 1) ∗ newSpec v.New' R P ⊢
      |={E}=> isPool p v.New' R P := by
  iintro ⟨Hp, #HNew⟩
  rw [isPool_unseal]; unfold isPoolDef
  iStructNamed Hp
  ipersist New
  imod inv_alloc nroot E (poolLocalInv p P) $$ [local'] with #Hinv
  · inext; unfold poolLocalInv; iexists v.local'; iframe
    ileft; ipureintro; exact hlocal
  imodintro
  iframe #

end wps

end sync

end Perennial
