/-
The proof of `strings.IndexByte`.
-/
module

public import Perennial.Spec.strings.IndexByte
public import Perennial.Spec.internal.stringslite.IndexByte

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

theorem strings.IndexByte.wp_proof
    (wp_IndexByte : internal.stringslite.IndexByte.spec (GF := GF) (hG := hG)) :
    strings.IndexByte.spec (GF := GF) (hG := hG) := fun s c => by
  wp_start
  wp_auto
  wp_apply wp_IndexByte
  iapply HΦ; itrivial

end proof

end Perennial
