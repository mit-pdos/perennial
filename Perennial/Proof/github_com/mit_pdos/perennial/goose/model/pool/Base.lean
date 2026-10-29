/-
Shared definitions of the proofs of the Go model of a `sync.Pool`'s state
(`github.com/mit-pdos/perennial/goose/model/pool`, used by `sync`'s `Pool`): `isPool s P`,
a model pool at `s` whose elements all satisfy `P`, and its initialization `init_Pool`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.github_com.mit_pdos.perennial.goose.model.pool
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.model.pool
public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.model.pool

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
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.model.pool.Assumptions]

/-- The lock invariant of the model pool at `s`: its elements `xs`, each satisfying `P`. -/
def poolInv (s : Loc) (P : GoAny → IProp GF) : IProp GF :=
  iprop(∃ (sl : GoSlice) (xs : List GoAny),
    "items" ∷ s.[Pool, go!"items"] ↦ sl ∗
    "Hsl" ∷ sl ↦* xs ∗
    "Hcap" ∷ ownSliceCap GoAny sl (DFrac.own 1) ∗
    "HP" ∷ [∗list] x ∈ xs, P x)

def isPoolDef (s : Loc) (P : GoAny → IProp GF) : IProp GF :=
  github_com.goose_lang.primitive.isMutex (s.[Pool, go!"mu"]) (poolInv s P)
/-- `s` is a model pool whose elements all satisfy `P` (sealed). -/
@[irreducible] def isPool (s : Loc) (P : GoAny → IProp GF) : IProp GF := isPoolDef s P
theorem isPool_unseal : @isPool = @isPoolDef := by funext; with_unfolding_all rfl

instance isPool_persistent (s : Loc) (P : GoAny → IProp GF) : Persistent (isPool s P) := by
  rw [isPool_unseal]; unfold isPoolDef; infer_instance

theorem init_Pool (s : Loc) (P : GoAny → IProp GF) (E : CoPset) :
    typedPointsto (GF := GF) s (zero_val Pool) (DFrac.own 1) ⊢ |={E}=> isPool s P := by
  iintro Hs
  rw [isPool_unseal]; unfold isPoolDef
  iStructNamed Hs
  iapply github_com.goose_lang.primitive.init_Mutex (poolInv s P) E _ $$ mu
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

end wps

end github_com.mit_pdos.perennial.goose.model.pool

end Perennial
