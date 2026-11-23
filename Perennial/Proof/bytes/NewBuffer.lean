/-
The proof of `bytes.NewBuffer`.
-/
module

public import Perennial.Spec.bytes.NewBuffer

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

theorem bytes.NewBuffer.wp_proof :
    bytes.NewBuffer.spec (GF := GF) (hG := hG) := by
  intro b bs
  wp_start as ⟨Hb, Hc⟩
  ihave %Hlen := ownSlice_len $$ Hb
  wp_auto
  iapply HΦ
  unfold bytes.ownBuffer
  iexists _, bs
  iframe
  ipureintro
  refine ⟨by word, by word, ?_⟩
  rw [show sint.nat (0 : w64) = 0 from rfl, List.drop_zero]

end proof

end Perennial
