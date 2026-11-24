/-
The proof of `runtime.Frames.Next` (its trusted model, `TrustedCode/runtime.lean`).
-/
module

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

theorem runtime.Frames.Next.wp_proof :
    runtime.Frames.Next.spec (GF := GF) (hG := hG) := fun f => by
  wp_start as Hf
  rw [show go.GoType.Named go!"runtime.Frames" [] = runtime.Frames.ty by with_unfolding_all rfl,
    show go.GoType.Named go!"runtime.Frame" [] = runtime.Frame.ty by with_unfolding_all rfl,
    show go.GoType.Named go!"runtime.Func" [] = runtime.Func.ty by with_unfolding_all rfl]
  unfold runtime.ownFrames
  icases Hf with ⟨%v, Hf⟩
  wp_auto
  wp_apply wp_ArbitraryInt as %pc -
  wp_apply wp_ArbitraryInt as %c -
  wp_join iprop(∃ fr : runtime.Frame, frame_ptr ↦ fr) with [frame] as ⟨%fr1, frame⟩
  · wp_apply wp_GoPrealloc as %l %Hl
    wp_join_done
  wp_apply fmt.wp_arbitraryString as %fn -
  wp_apply fmt.wp_arbitraryString as %file -
  wp_apply wp_ArbitraryInt as %line -
  wp_apply wp_ArbitraryInt as %sl -
  wp_apply wp_ArbitraryInt as %entry -
  wp_apply wp_ArbitraryInt as %m -
  iapply HΦ
  iexists _
  iexact Hf

end proof

end Perennial
