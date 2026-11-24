/-
The proof of `fmt.(*pp).fmtString`.
-/
module

public import Perennial.Spec.fmt.pp__fmtString
public import Perennial.Spec.fmt.fmt__fmtS
public import Perennial.Spec.fmt.fmt__fmtSx
public import Perennial.Spec.fmt.fmt__fmtQ

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.pp.fmtString.wp_proof (wp_fmtS : fmt.fmt.fmtS.spec (GF := GF) (hG := hG))
    (wp_fmtSx : fmt.fmt.fmtSx.spec (GF := GF) (hG := hG))
    (wp_fmtQ : fmt.fmt.fmtQ.spec (GF := GF) (hG := hG)) :
    fmt.pp.fmtString.spec (GF := GF) (hG := hG) :=
    fun p x bs wid prec v verb hverb hshort => by
  rcases hverb with rfl | rfl | rfl | rfl
  all_goals
    wp_start as Hp
    unfold isPrinterA
    icases Hp with ⟨Hb, Hf, Hib, Hrest⟩
    unfold fmtOwn
    icases Hf with ⟨Hfb, Hff, Hfw, Hfp⟩
    wp_auto
  · wp_apply wp_fmtS _ (p.[pp, go!"buf"]) noFlags wid prec bs v rfl (Or.inl rfl) $$ [Hfb Hff Hfw Hfp Hb]
      as ⟨Hf, Hb⟩
    · unfold fmtOwn; iframe
    iapply HΦ
    iexists v
    isplitr
    · ipureintro; right; simp
    unfold fmtOwn
    iframe
  · wp_apply wp_fmtS _ (p.[pp, go!"buf"]) noFlags wid prec bs v rfl (Or.inl rfl) $$ [Hfb Hff Hfw Hfp Hb]
      as ⟨Hf, Hb⟩
    · unfold fmtOwn; iframe
    iapply HΦ
    iexists v
    isplitr
    · ipureintro; right; simp
    unfold fmtOwn
    iframe
  · rw [show ldigits = #(hexDigits false) from rfl]
    wp_apply wp_fmtSx _ (p.[pp, go!"buf"]) noFlags wid prec bs v false rfl rfl rfl rfl (hshort rfl) $$ [Hfb Hff Hfw Hfp Hb]
      as ⟨Hf, Hb⟩
    · unfold fmtOwn; iframe
    iapply HΦ
    iexists (bytesHex false v)
    isplitr
    · ipureintro; right; simp
    unfold fmtOwn
    iframe
  · wp_apply wp_fmtQ _ (p.[pp, go!"buf"]) noFlags wid prec bs v rfl rfl rfl (Or.inl rfl)
      $$ [Hfb Hff Hfw Hfp Hib Hb] as ⟨%o, Hf, Hib, Hb⟩
    · unfold fmtOwn; iframe
    iapply HΦ
    iexists o
    isplitr
    · ipureintro; left; rfl
    unfold fmtOwn
    iframe

end proof

end Perennial
