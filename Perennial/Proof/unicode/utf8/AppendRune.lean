/-
The proof of `unicode/utf8.AppendRune`.
-/
module

public import Perennial.Spec.unicode.utf8.AppendRune
public import Perennial.Spec.unicode.utf8.appendRuneNonASCII

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : unicode.utf8.Assumptions]

attribute [-instance] go.SliceSemantics.composite_literal_slice

theorem unicode.utf8.AppendRune.wp_proof
    (wp_appendRuneNonASCII : unicode.utf8.appendRuneNonASCII.spec (GF := GF) (hG := hG)) :
    unicode.utf8.AppendRune.spec (GF := GF) (hG := hG) := by
  intro p bs r
  wp_start as ⟨Hp, Hcap⟩
  wp_auto
  wp_if_destruct
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_slice_append_undo (V := w8) (t := go.byte) p bs _ _ _ $$ [$Hp $Hcap $Hsl]
      as %p' ⟨Hp', Hcap', -, Hundo⟩
    iapply HΦ
    iexists _
    iframe
  · wp_apply wp_appendRuneNonASCII $$ [$Hp $Hcap] as %p' Hp'
    iapply HΦ
    iexact Hp'

end proof

end Perennial
