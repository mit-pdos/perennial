/-
The proof of `internal.bytealg.CompareString`.
-/
module

public import Perennial.Spec.internal.bytealg.CompareString
public import Perennial.Spec.internal.bytealg.abigen_runtime_cmpstring

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

theorem internal.bytealg.CompareString.wp_proof
    (wp_abigen_runtime_cmpstring :
      internal.bytealg.abigen_runtime_cmpstring.spec (GF := GF) (hG := hG)) :
    internal.bytealg.CompareString.spec (GF := GF) (hG := hG) := fun a b => by
  wp_start
  wp_auto
  wp_apply wp_abigen_runtime_cmpstring
  iapply HΦ; itrivial

end proof

end Perennial
