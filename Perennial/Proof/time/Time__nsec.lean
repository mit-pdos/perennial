/-
The proof of `time.Time.nsec`.
-/
module

public import Perennial.Spec.time.Time__nsec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.Time.nsec.wp_proof :
    time.Time.nsec.spec (GF := GF) (hG := hG) := by
  intro t tv
  wp_start as Ht
  wp_auto
  wp_end

end proof

end Perennial
