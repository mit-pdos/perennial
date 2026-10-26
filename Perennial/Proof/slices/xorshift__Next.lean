/-
The proof of `slices.xorshift.Next`.
-/
module

public import Perennial.Spec.slices.xorshift__Next
public import Perennial.Proof.slices.PartitionBasics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.xorshift.Next.wp_proof : slices.xorshift.Next.spec (GF := GF) (hG := hG) := by
  intro r v
  wp_start as Hr
  wp_auto
  wp_end

end proof

end Perennial
