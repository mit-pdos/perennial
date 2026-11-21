/-
The proof of `strings.NewReplacer`.
-/
module

public import Perennial.Spec.strings.NewReplacer

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

theorem strings.NewReplacer.wp_proof :
    strings.NewReplacer.spec (GF := GF) (hG := hG) := by
  intro oldnew ss dq Heven
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  wp_auto
  wp_if_destruct
  · exfalso
    have h2 := congrArg BitVec.toInt Hif
    rw [BitVec.toInt_srem, show (W64 2).toInt = 2 from rfl, show (W64 1).toInt = 1 from rfl,
      Int.tmod_eq_emod_of_nonneg Hlen.2] at h2
    have := Hlen.1
    word
  wp_apply (wp_slice_append_dfrac (V := GoString) slice.nil [] (DFrac.own 1) oldnew ss dq)
    $$ [Hs] as %sl ⟨Hsl, Hcap, Hs⟩
  · iframe Hs
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; exact DFrac.valid_own_one
  iapply HΦ
  iframe Hs
  unfold strings.ownReplacer
  iexists sl
  rw [List.nil_append]
  iframe

end proof

end Perennial
