/-
The proof of `strings.Builder.Grow`.
-/
module

public import Perennial.Spec.strings.Builder__Grow
public import Perennial.Spec.strings.Builder__copyCheck
public import Perennial.Spec.strings.Builder__grow_

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

set_option maxHeartbeats 2000000 in
theorem strings.Builder.Grow.wp_proof
    (wp_copyCheck : strings.Builder.copyCheck.spec (GF := GF) (hG := hG))
    (wp_grow : strings.Builder.grow.spec (GF := GF) (hG := hG)) :
    strings.Builder.Grow.spec (GF := GF) (hG := hG) := by
  intro l s n
  wp_start as ⟨Hown, %Hn⟩
  unfold strings.ownBuilder
  icases Hown with ⟨%used, %buf, %dq, %Hnn, Haddr, Hbf, Hbuf, Hcap, %Hdq⟩
  ihave %Hcwf := ownSliceCap_wf $$ Hcap
  ihave %Hblen := ownSlice_len $$ Hbuf
  wp_auto
  wp_apply wp_copyCheck $$ [Haddr] as Haddr
  · iframe Haddr; ipureintro; exact Hnn
  try wp_auto
  wp_if_destruct
  · exfalso; have : sint.Z (W64 0) = 0 := rfl; omega
  try wp_auto
  wp_if_destruct
  · wp_apply wp_grow $$ [$Haddr $Hbf $Hbuf] as Hown
    · ipureintro
      refine ⟨Hnn, Hn.1, ?_⟩
      have h1 : sint.Z (buf.cap - buf.len) = sint.Z buf.cap - sint.Z buf.len := by word
      have h2 : (s.length : Int) = sint.Z buf.len := by rw [Hblen.1]; word
      omega
    try wp_auto
    unfold strings.ownBuilder
    iapply HΦ $$ Hown
  · try wp_auto
    iapply HΦ
    iexists true, buf, dq
    iframe Haddr Hbf Hbuf Hcap
    ipureintro; exact ⟨Hnn, Hdq⟩

end proof

end Perennial
