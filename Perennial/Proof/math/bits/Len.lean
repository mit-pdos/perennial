/-
The proof of `math.bits.Len`.
-/
module

public import Perennial.Spec.math.bits.Len
public import Perennial.Spec.math.bits.Len64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

theorem math.bits.Len.wp_proof
    (wp_Len64 : math.bits.Len64.spec (GF := GF) (hG := hG)) :
    math.bits.Len.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_Len64 with %l %Hl
  wp_end

end proof

end Perennial
