/-
The proof of `strings.TrimLeft`, for an ASCII cutset.
-/
module

public import Perennial.Spec.strings.TrimLeft
public import Perennial.Spec.strings.trimLeftByte
public import Perennial.Spec.strings.makeASCIISet
public import Perennial.Spec.strings.trimLeftASCII
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

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

theorem strings.TrimLeft.wp_proof
    (wp_trimLeftByte : strings.trimLeftByte.spec (GF := GF) (hG := hG))
    (wp_makeASCIISet : strings.makeASCIISet.spec (GF := GF) (hG := hG))
    (wp_trimLeftASCII : strings.trimLeftASCII.spec (GF := GF) (hG := hG)) :
    strings.TrimLeft.spec (GF := GF) (hG := hG) := by
  intro s cutset
  wp_start as %Hascii
  wp_auto
  wp_if_destruct
  · -- `s == ""`
    try wp_auto
    rw [show strings.trimLeft [] cutset = [] from rfl]
    iapply HΦ
    itrivial
  wp_if_destruct
  · -- `cutset == ""`
    try wp_auto
    rw [show strings.trimLeft s [] = s by
      unfold strings.trimLeft; cases s with
      | nil => rfl
      | cons b t => simp]
    iapply HΦ
    itrivial
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hcl
  wp_if_destruct
  · -- `len(cutset) == 1`
    have H1 : cutset.length = 1 := by revert Hif; word
    obtain ⟨c, rfl⟩ : ∃ c, cutset = [c] := by
      match cutset, H1 with
      | [c], _ => exact ⟨c, rfl⟩
    have Hc : uint.Z c < 128 := Hascii c (by simp)
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_apply wp_trimLeftByte
      rw [show strings.trimLeft s [c] = s.dropWhile (fun b => decide (b = c)) by
        simp [strings.trimLeft]]
      iapply HΦ
      itrivial
    · exfalso; revert Hif; word
  try wp_auto
  wp_apply wp_makeASCIISet as %aset %ok ⟨%Hok, %Hlen, %Hhas⟩
  have Hhas := Hhas (Hok.2 Hascii)
  rw [show ok = true from Hok.2 Hascii]
  try wp_auto
  irename «as» => Has
  wp_apply wp_trimLeftASCII $$ Has as Has
  rw [show s.dropWhile (strings.asciiSetHas aset) = strings.trimLeft s cutset by
    unfold strings.trimLeft; congr 1; funext b; exact Hhas b]
  iapply HΦ
  itrivial

end proof

end Perennial
