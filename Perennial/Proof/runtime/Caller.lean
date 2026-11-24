/-
The proof of `runtime.Caller`.
-/
module

public import Perennial.Spec.runtime.Caller
public import Perennial.Spec.runtime.callers_
public import Perennial.Spec.runtime.CallersFrames
public import Perennial.Spec.runtime.Frames__Next

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

theorem runtime.Caller.wp_proof
    (wp_callers : runtime.callers.spec (GF := GF) (hG := hG))
    (wp_CallersFrames : runtime.CallersFrames.spec (GF := GF) (hG := hG))
    (wp_Frames__Next : runtime.Frames.Next.spec (GF := GF) (hG := hG)) :
    runtime.Caller.spec (GF := GF) (hG := hG) := fun skip => by
  wp_start
  wp_auto
  wp_apply wp_slice_make2 (V := w64) $$ [] as %b ⟨Hb, -⟩
  · ipureintro; word
  wp_apply wp_callers $$ Hb as %n Hn
  wp_if_destruct
  · iapply HΦ
    itrivial
  · wp_apply wp_CallersFrames as %f Hf
    wp_apply wp_Frames__Next $$ Hf as %fr %more Hf
    iapply HΦ
    itrivial

end proof

end Perennial
