/-
The proof of `fmt.(*fmt).pad`.
-/
module

public import Perennial.Spec.fmt.fmt__pad
public import Perennial.Spec.fmt.buffer__write
public import Perennial.Spec.fmt.fmt__writePadding
public import Perennial.Spec.unicode.utf8.RuneCount

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.fmt.pad.wp_proof
    (wp_write : fmt.buffer.write.spec (GF := GF) (hG := hG))
    (wp_writePadding : fmt.fmt.writePadding.spec (GF := GF) (hG := hG))
    (wp_RuneCount : unicode.utf8.RuneCount.spec (GF := GF) (hG := hG)) :
    fmt.fmt.pad.spec (GF := GF) (hG := hG) :=
    fun f b F wid prec bs sl ys q Hcase => by
  wp_start as ⟨Hf, Hb, Hs⟩
  unfold fmt.fmtOwn
  icases Hf with ⟨Hbuf, HF, Hw, Hp⟩
  wp_auto
  cases hw : F.widPresent' <;> simp only [Bool.not_false, Bool.not_true]
  · wp_auto
    wp_apply wp_write $$ [Hb Hs] as ⟨Hb, Hs⟩
    · iframe
    wp_auto
    iapply HΦ
    iframe
  · wp_auto
    wp_if_destruct
    · wp_apply wp_write $$ [Hb Hs] as ⟨Hb, Hs⟩
      · iframe
      wp_auto
      iapply HΦ
      iframe
    obtain ⟨Hascii, Hwid0, Hwid⟩ :
        (∀ c ∈ ys, uint.Z c < 128) ∧ 0 ≤ sint.Z wid ∧ sint.Z wid ≤ ys.length := by
      rcases Hcase with h | h | h
      · simp [hw] at h
      · exact absurd h Hif
      · exact h
    ihave %Hlen := ownSlice_len $$ Hs
    wp_apply wp_RuneCount sl ys q Hascii $$ [Hs] as Hs
    · iframe
    have Hn : sint.Z (wid - W64 (ys.length : Int)) ≤ 0 := by word
    cases hm : F.minus' <;> simp only [Bool.not_false, Bool.not_true]
    · wp_auto
      wp_apply wp_writePadding f b F wid prec _ Hn $$ [Hbuf HF Hw Hp] as Hf
      · unfold fmt.fmtOwn; iframe
      unfold fmt.fmtOwn
      icases Hf with ⟨Hbuf, HF, Hw, Hp⟩
      wp_auto
      wp_apply wp_write $$ [Hb Hs] as ⟨Hb, Hs⟩
      · iframe
      iapply HΦ
      iframe
    · wp_auto
      wp_apply wp_write $$ [Hb Hs] as ⟨Hb, Hs⟩
      · iframe
      wp_auto
      wp_apply wp_writePadding f b F wid prec _ Hn $$ [Hbuf HF Hw Hp] as Hf
      · unfold fmt.fmtOwn; iframe
      iapply HΦ
      unfold fmt.fmtOwn
      iframe

end proof

end Perennial
