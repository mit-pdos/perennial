/-
The proof of `strings.Split`.
-/
module

public import Perennial.Spec.strings.Split
public import Perennial.Spec.strings.genSplit

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

theorem strings.Split.wp_proof
    (wp_genSplit : strings.genSplit.spec (GF := GF) (hG := hG)) :
    strings.Split.spec (GF := GF) (hG := hG) := fun s sep Hsep Hs => by
  wp_start
  wp_auto
  wp_apply wp_genSplit s sep Hsep Hs as %sl ⟨Hsl, Hcap⟩
  iapply HΦ
  iframe

end proof

end Perennial
