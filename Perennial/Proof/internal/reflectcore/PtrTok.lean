/-
The proof of `internal.reflectcore.PtrTok`.
-/
module

public import Perennial.Spec.internal.reflectcore.PtrTok
public import Perennial.Spec.internal.reflectcore.ptrTok_

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

theorem internal.reflectcore.PtrTok.wp_proof
    (wp_ptrTok : internal.reflectcore.ptrTok.spec (GF := GF) (hG := hG)) :
    internal.reflectcore.PtrTok.spec (GF := GF) (hG := hG) := fun T v => by
  wp_start
  wp_apply wp_FuncResolveAt (go.Shape.deref go.Shape.self) _ _ _ [T] rfl
  rw [show (go!"internal/reflectcore.ptrTok" : GoString) = ptrTok from rfl]
  wp_apply wp_ptrTok T _
  iapply HΦ
  itrivial

end proof

end Perennial
