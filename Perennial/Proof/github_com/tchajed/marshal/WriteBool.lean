/-
The proof of `github.com/tchajed/marshal.WriteBool`.
-/
module

public import Perennial.Spec.github_com.tchajed.marshal.WriteBool

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]
-- Workaround (as in `unittest`): `wp_auto` unfolds slice literals
-- (`composite_literal_slice` is a pure step), but `wp_slice_literal` expects
-- the literal to be folded.
attribute [-instance] go.SliceSemantics.composite_literal_slice

theorem github_com.tchajed.marshal.WriteBool.wp_proof :
    github_com.tchajed.marshal.WriteBool.spec (GF := GF) (hG := hG) := fun s vs b => by
  wp_start as ⟨Hs, Hcap⟩
  wp_auto
  cases b <;> (
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_slice_append (V := w8) (t := go.byte) s vs _ _ _ $$ [$Hs $Hcap $Hsl]
      as %s' ⟨Hs', Hcap', -⟩
    iapply HΦ
    iframe Hcap'
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexact Hs')

end proof

end Perennial
