/-
The proof of `fmt.(*fmt).fmtBx`.
-/
module

public import Perennial.Spec.fmt.fmt__fmtBx
public import Perennial.Spec.fmt.fmt__fmtSbx

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

theorem fmt.fmt.fmtBx.wp_proof (wp_fmtSbx : fmt.fmt.fmtSbx.spec (GF := GF) (hG := hG)) :
    fmt.fmt.fmtBx.spec (GF := GF) (hG := hG) :=
    fun f b F wid prec bs sl ys q upper hp hw hs hsp => by
  wp_start as ⟨Hf, Hb, Hsl⟩
  wp_auto
  wp_apply wp_fmtSbx f b F wid prec bs go!"" sl ys q upper hp hw hs hsp $$ [Hf Hb Hsl]
    as ⟨Hf, Hb, Hsl⟩
  · iframe
  iapply HΦ
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  by_cases hnil : sl = slice.nil
  · subst hnil
    have hys : ys = [] := List.eq_nil_of_length_eq_zero (by have := Hlen.1; simp [slice.nil] at this; rw [this]; rfl)
    subst hys
    simp only [↓reduceIte]
    iframe
  · simp only [hnil, ↓reduceIte]
    iframe

end proof

end Perennial
