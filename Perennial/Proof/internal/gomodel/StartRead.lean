/-
The proof of `internal.gomodel.StartRead`.
-/
module

public import Perennial.Spec.internal.gomodel.StartRead

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.gomodel.Assumptions]

theorem internal.gomodel.StartRead.wp_proof :
    internal.gomodel.StartRead.spec (GF := GF) (hG := hG) := by
  intro T V l x
  wp_start as Hl
  wp_bind (_root_.Perennial.StartRead _)
  wp_apply_core (wp_start_read l DFrac.discard #x) $$ Hl
  iintro -
  wp_pures
  iapply HΦ
  itrivial

end proof

end Perennial
