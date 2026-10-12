/-
The proof of `strings.Index'`.
-/
module

public import Perennial.Spec.strings.Index
public import Perennial.Spec.internal.stringslite.Index

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.Index'.wp_proof
    (wp_Index : internal.stringslite.Index'.spec (GF := GF) (hG := hG)) :
    strings.Index'.spec (GF := GF) (hG := hG) := fun s sub => by
  wp_start
  wp_auto
  wp_apply wp_Index
  iapply HΦ; itrivial

end proof

end Perennial
