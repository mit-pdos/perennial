/-
The proof of `strings.Compare`.
-/
module

public import Perennial.Spec.strings.Compare
public import Perennial.Spec.internal.bytealg.CompareString

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.Compare.wp_proof
    (wp_CompareString : internal.bytealg.CompareString.spec (GF := GF) (hG := hG)) :
    strings.Compare.spec (GF := GF) (hG := hG) := fun a b => by
  wp_start
  wp_auto
  wp_apply wp_CompareString
  iapply HΦ; itrivial

end proof

end Perennial
