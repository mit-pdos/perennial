/-
The proof of `unicode/utf8.DecodeRuneInString`.
-/
module

public import Perennial.Spec.unicode.utf8.DecodeRuneInString
public import Perennial.Spec.unicode.utf8.decodeRuneInStringSlow
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
variable [package_sem : unicode.utf8.Assumptions]

theorem unicode.utf8.DecodeRuneInString.wp_proof
    (wp_decodeRuneInStringSlow : unicode.utf8.decodeRuneInStringSlow.spec (GF := GF) (hG := hG)) :
    unicode.utf8.DecodeRuneInString.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as #Hpkg
  wp_auto
  wp_if_destruct
  · wp_apply wp_decodeRuneInStringSlow as %r %size %Hsz
    iapply HΦ; ipureintro; exact Hsz
  obtain ⟨c, rest, rfl⟩ := List.exists_cons_of_ne_nil Hif
  wp_auto
  wp_if_destruct
  · iapply HΦ; ipureintro; right
    refine ⟨List.cons_ne_nil _ _, by word, by simp only [List.length_cons]; word⟩
  · wp_apply wp_decodeRuneInStringSlow as %r %size %Hsz
    iapply HΦ; ipureintro; exact Hsz

end proof

end Perennial
