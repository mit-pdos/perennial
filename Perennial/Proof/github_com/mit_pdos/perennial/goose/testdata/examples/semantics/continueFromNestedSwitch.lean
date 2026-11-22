/-
The proof of `continueFromNestedSwitch` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.continueFromNestedSwitch

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.continueFromNestedSwitch.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.continueFromNestedSwitch.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  ihave HI : (∃ i n : w64,
      "i" ∷ i_ptr ↦ i ∗
      "n" ∷ n_ptr ↦ n ∗
      "%Hi" ∷ ⌜uint.Z i ≤ 6 ∧ 2 * uint.Z n = uint.Z i + uint.Z i % 2⌝ : IProp GF) $$ [i n]
  · iexists _, _
    iframe
    ipureintro; exact ⟨by decide, rfl⟩
  wp_for HI
  wp_if_destruct
  · ihave HJ : (∃ j n' : w64,
        "j" ∷ j_ptr ↦ j ∗
        "n" ∷ n_ptr ↦ n' ∗
        "%Hj" ∷ ⌜uint.Z j ≤ 2 ∧ (1 ≤ uint.Z j → uint.Z i % 2 = 0) ∧
          uint.Z n' = uint.Z n + uint.Z j / 2⌝ : IProp GF) $$ [j n]
    · iexists _, _
      iframe
      ipureintro; word
    wp_for HJ
    wp_if_destruct
    · repeat (first | wp_if_destruct | wp_auto)
      · -- odd `i`: `continue L` leaves the inner loop without its post statement
        wp_for_post
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        have h1 : uint.Z i % 2 = 1 := by word
        constructor <;> word
      · wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        have h0 : uint.Z i % 2 = 0 := by word
        refine ⟨by word, fun _ => h0, by word⟩
      · wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        have hj : uint.Z j = 1 := by word
        have h0 := Hj.2.1 (by omega)
        refine ⟨by word, fun _ => h0, by word⟩
    · -- the inner loop ends at `j = 2`
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      have hj : uint.Z j = 2 := by word
      have h0 := Hj.2.1 (by omega)
      constructor <;> word
  · have : n = W64 3 := by word
    subst this
    iapply HΦ
    iexact Hpre

end proof

end Perennial
