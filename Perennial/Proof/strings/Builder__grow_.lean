/-
The proof of `strings.Builder.grow`.
-/
module

public import Perennial.Spec.strings.Builder__grow_
public import Perennial.Spec.internal.bytealg.MakeNoZero

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.Builder.grow.wp_proof
    (wp_MakeNoZero : internal.bytealg.MakeNoZero.spec (GF := GF) (hG := hG)) :
    strings.Builder.grow.spec (GF := GF) (hG := hG) := fun b addr buf s n Hn => by
  wp_start as ⟨Hb, Hs, Hcap⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  have Hmax := Hn.2
  unfold internal.bytealg.maxAlloc at Hmax
  wp_auto
  have Hm : sint.Z (W64 2 * buf.cap + n) = 2 * sint.Z buf.cap + sint.Z n := by word
  wp_apply wp_MakeNoZero (W64 2 * buf.cap + n)
    ⟨by rw [Hm]; omega, by rw [Hm]; exact Hn.2⟩ as %sl ⟨%bs0, %Hbs0, Hsl, Hslcap⟩
  ihave %Hsllen := ownSlice_len $$ Hsl
  ihave %Hslwf := ownSlice_wf $$ Hsl
  rw [Hbs0] at Hsllen
  have Hk : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z buf.len ∧ sint.Z buf.len ≤ sint.Z sl.len :=
    ⟨by word, by word, by word⟩
  rw [ite_eq_left ⟨Hk.1, Hk.2.1, by omega⟩]
  icases ownSlice_slice_with_cap (W64 0) buf.len sl _ Hk $$ [Hsl Hslcap] with ⟨-, Hnew, Hnewcap⟩
  · iframe
  wp_auto
  wp_apply wp_slice_copy (V := w8) (t := go.byte) _ _ buf s (DFrac.own 1) $$ [Hnew Hs]
    as %m ⟨-, Hnew, Hs⟩
  · iframe
  try wp_auto
  iapply HΦ
  iexists _
  iframe
  have Hsub : (subslice (sint.nat (W64 0)) (sint.nat buf.len) bs0).length = s.length := by
    simp only [subslice, List.length_take, List.length_drop, Hbs0]; word
  rw [Hsub, List.take_length, List.drop_eq_nil_of_le (Nat.le_of_eq Hsub), List.append_nil]
  iexact Hnew

end proof

end Perennial
