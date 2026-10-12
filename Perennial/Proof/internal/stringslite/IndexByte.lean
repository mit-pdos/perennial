/-
The proof of `internal.stringslite.IndexByte`.
-/
module

public import Perennial.Spec.internal.stringslite.IndexByte
public import Perennial.Spec.internal.bytealg.IndexByteString

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.stringslite.Assumptions]

theorem internal.stringslite.IndexByte.wp_proof
    (wp_IndexByteString : internal.bytealg.IndexByteString.spec (GF := GF) (hG := hG)) :
    internal.stringslite.IndexByte.spec (GF := GF) (hG := hG) := fun s c => by
  wp_start
  wp_auto
  wp_apply wp_IndexByteString
  iapply HΦ; itrivial

end proof

end Perennial
