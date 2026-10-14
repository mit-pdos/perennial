/-
The proof of `strings.HasPrefix`.
-/
module

public import Perennial.Spec.strings.HasPrefix
public import Perennial.Spec.internal.stringslite.HasPrefix

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

theorem strings.HasPrefix.wp_proof
    (wp_HasPrefix : internal.stringslite.HasPrefix.spec (GF := GF) (hG := hG)) :
    strings.HasPrefix.spec (GF := GF) (hG := hG) := fun s pfx => by
  wp_start
  wp_auto
  wp_apply wp_HasPrefix
  iapply HΦ; itrivial

end proof

end Perennial
