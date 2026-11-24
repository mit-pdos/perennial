/-
The proof of `strconv.quoteWith`.
-/
module

public import Perennial.Spec.strconv.quoteWith
public import Perennial.Spec.strconv.appendQuotedWith
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
variable [package_sem : strconv.Assumptions]

theorem strconv.quoteWith.wp_proof
    (wp_appendQuotedWith : strconv.appendQuotedWith.spec (GF := GF) (hG := hG)) :
    strconv.quoteWith.spec (GF := GF) (hG := hG) := by
  intro s quote ASCIIonly
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len_maxAddr as %Hs
  have hcap := strconv.quoteWith_cap s.length (by unfold maxAddr at Hs; exact Hs)
  wp_apply wp_slice_make3 (V := w8) (t := go.byte) _ _ ⟨by decide, by simpa using hcap⟩
    as %b ⟨Hb, Hcap, -⟩
  try wp_auto
  wp_apply wp_appendQuotedWith _ _ _ _ _ $$ [$Hb $Hcap] as %b' ⟨%q, Hb', -⟩
  wp_apply wp_bytes_to_string $$ [$Hb'] as -
  iapply HΦ
  itrivial

end proof

end Perennial
