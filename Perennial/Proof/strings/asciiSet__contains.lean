/-
The proof of `strings.asciiSet.contains`.
-/
module

public import Perennial.Spec.strings.asciiSet__contains

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

theorem strings.asciiSet.contains.wp_proof :
    strings.asciiSet.contains.spec (GF := GF) (hG := hG) := by
  intro aset v dq c
  wp_start as Has
  obtain ⟨vs⟩ := v
  ihave %Hlen := array_len aset dq 8 vs $$ Has
  wp_auto
  have hi : sint.Z (W64 (uint.Z (c / W8 32))) = ((c.toNat / 32 : Nat) : Int) := by word
  rw [ite_eq_left (by word)]
  have hlt : c.toNat / 32 < vs.length := by have := c.isLt; omega
  icases array_acc (V := w32) aset (sint.Z (W64 (uint.Z (c / W8 32)))) dq 8 ⟨vs⟩
    vs[c.toNat / 32] (by word)
    (by rw [hi, Int.toNat_natCast]; exact List.getElem?_eq_getElem hlt) $$ Has with ⟨Hel, Hclose⟩
  wp_auto
  ihave Has := Hclose $$ Hel
  rw [hi, Int.toNat_natCast, List.set_getElem_self]
  rw [show strings.asciiSetHas ⟨vs⟩ c =
      !decide (vs[c.toNat / 32] &&& W32 1 <<< W64 (uint.Z (c % W8 32)) = W32 0) by
    simp only [strings.asciiSetHas, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      Option.getD_some]]
  iapply HΦ $$ Has

end proof

end Perennial
