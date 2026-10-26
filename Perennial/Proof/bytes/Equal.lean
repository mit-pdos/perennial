/-
The proof of `bytes.Equal`.
-/
module

public import Perennial.Spec.bytes.Equal

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

theorem bytes.Equal.wp_proof :
    bytes.Equal.spec (GF := GF) (hG := hG) := by
  intro sl_b0 sl_b1 d0 d1 b0 b1
  wp_start
  iNamed Hpre
  wp_auto
  wp_apply wp_bytes_to_string $$ Hb0 with Hb0
  wp_apply wp_bytes_to_string $$ Hb1 with Hb1
  iapply HΦ
  iframe

end proof

end Perennial
