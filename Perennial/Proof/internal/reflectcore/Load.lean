/-
The proof of `internal.reflectcore.Load`.
-/
module

public import Perennial.Spec.internal.reflectcore.Load
public import Perennial.Spec.internal.reflectcore.load_

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

theorem internal.reflectcore.Load.wp_proof
    (wp_load : internal.reflectcore.load.spec (GF := GF) (hG := hG)) :
    internal.reflectcore.Load.spec (GF := GF) (hG := hG) := by
  constructor
  · intro V _ _ T Tu _ _ q dq x hT hn
    wp_start as Hq
    wp_apply wp_FuncResolveAt (go.Shape.deref go.Shape.self) _ _ _ [T] rfl
    rw [show (go!"internal/reflectcore.load" : GoString) = load from rfl]
    wp_apply wp_load.1 q dq x hT hn $$ [$Hq] as Hq
    iapply HΦ
    iexact Hq
  · intro T elems _ q dq i
    wp_start as Hq
    wp_apply wp_FuncResolveAt (go.Shape.deref go.Shape.self) _ _ _ [T] rfl
    rw [show (go!"internal/reflectcore.load" : GoString) = load from rfl]
    wp_apply wp_load.2 q dq i $$ [$Hq] as Hq
    iapply HΦ
    iexact Hq

end proof

end Perennial
