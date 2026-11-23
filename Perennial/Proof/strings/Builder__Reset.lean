/-
The proof of `strings.Builder.Reset`.
-/
module

public import Perennial.Spec.strings.Builder__Reset

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.Builder.Reset.wp_proof :
    strings.Builder.Reset.spec (GF := GF) (hG := hG) := by
  intro l s
  wp_start as Hown
  unfold strings.ownBuilder
  icases Hown with ⟨%used, %buf, %dq, %Hnn, Haddr, Hbf, Hbuf, Hcap, %Hdq⟩
  rw [show go.GoType.Named go!"strings.Builder" [] = strings.Builder.ty by with_unfolding_all rfl]
  wp_auto
  iapply HΦ
  iexists used, slice.nil, DFrac.own 1
  isplitr
  · ipureintro; exact Hnn
  iframe Haddr Hbf
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply ownSliceCap_nil
  ipureintro; exact DFrac.valid_own_one

end proof

end Perennial
