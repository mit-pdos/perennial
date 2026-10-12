/-
The proof of `fmt.Printf`.
-/
module

public import Perennial.Spec.fmt.Printf

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.Printf.wp_proof :
    fmt.Printf.spec (GF := GF) (hG := hG) := by
  intro format args_sl xs dq Hxs
  wp_start as Hsl
  iapply HΦ
  iframe

end proof

end Perennial
