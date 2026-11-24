/-
The proof of `internal.reflectcore.Store`.
-/
module

public import Perennial.Spec.internal.reflectcore.Store
public import Perennial.Spec.internal.reflectcore.store_

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectcore.Assumptions]

theorem internal.reflectcore.Store.wp_proof
    (wp_store : internal.reflectcore.store.spec (GF := GF) (hG := hG)) :
    internal.reflectcore.Store.spec (GF := GF) (hG := hG) := by
  constructor
  · intro V _ _ T Tu _ _ l v y hT
    wp_start as Hl
    wp_apply wp_FuncResolveAt (go.Shape.deref go.Shape.self) _ _ _ [T] rfl
    rw [show (go!"internal/reflectcore.store" : GoString) = store from rfl]
    wp_apply wp_store.1 l v y hT $$ [$Hl] as Hl
    iapply HΦ
    iexact Hl
  · intro V _ _ T elems _ _ l v y ii hts hy
    wp_start as Hl
    wp_apply wp_FuncResolveAt (go.Shape.deref go.Shape.self) _ _ _ [T] rfl
    rw [show (go!"internal/reflectcore.store" : GoString) = store from rfl]
    wp_apply wp_store.2 l v y ii hts hy $$ [$Hl] as Hl
    iapply HΦ
    iexact Hl

end proof

end Perennial
