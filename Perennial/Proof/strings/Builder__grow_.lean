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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

set_option maxHeartbeats 2000000 in
theorem strings.Builder.grow.wp_proof
    (wp_MakeNoZero : internal.bytealg.MakeNoZero.spec (GF := GF) (hG := hG)) :
    strings.Builder.grow.spec (GF := GF) (hG := hG) := by
  intro l used buf dq s n
  wp_start as ⟨%Hnn, Haddr, Hbf, Hbuf, %Hb⟩
  ihave %Hbwf := ownSlice_wf $$ Hbuf
  ihave %Hblen := ownSlice_len $$ Hbuf
  wp_auto
  have hnew : sint.Z (W64 2 * buf.cap + n) = 2 * sint.Z buf.cap + sint.Z n := by word
  wp_apply wp_MakeNoZero as %nb %bs ⟨Hnb, Hnbcap, %Hbs⟩
  · ipureintro; omega
  ihave %Hnbwf := ownSlice_wf $$ Hnb
  ihave %Hnblen := ownSlice_len $$ Hnb
  have hlen : sint.Z buf.len ≤ sint.Z nb.len := by
    have : sint.Z nb.len = sint.Z (W64 2 * buf.cap + n) := by
      have h1 := Hnblen.1; rw [Hbs] at h1
      have h2 := Hnblen.2
      have h3 : 0 ≤ sint.Z (W64 2 * buf.cap + n) := by omega
      have e : ∀ x : w64, sint.nat x = (sint.Z x).toNat := fun _ => rfl
      rw [e, e] at h1
      omega
    omega
  try wp_auto
  rw [if_pos ⟨by decide, by word, by omega⟩]
  icases ownSlice_slice_with_cap (W64 0) buf.len nb bs ⟨by decide, by word, hlen⟩
    $$ [$Hnb $Hnbcap] with ⟨-, Hnew, Hnewcap⟩
  wp_auto
  wp_apply wp_slice_copy (V := w8) _ _ buf s dq $$ [$Hnew $Hbuf] as %m ⟨%Hm, Hnew, -⟩
  try wp_auto
  have hsl : (subslice 0 (sint.nat buf.len) bs).length = s.length := by
    simp only [subslice, List.length_drop, List.length_take]; word
  rw [List.drop_eq_nil_of_le (Nat.le_of_eq hsl), hsl, List.take_length, List.append_nil]
  iapply HΦ
  unfold strings.ownBuilder
  iexists used, slice.slice nb w8 (W64 0) buf.len, DFrac.own 1
  iframe Haddr Hbf Hnew Hnewcap
  ipureintro; exact ⟨Hnn, DFrac.valid_own_one⟩

end proof

end Perennial
