/-
The proof of `countRune` (a goose semantics test, `range_string.go`): a range loop
over a string, by `wp_string_for_range`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.countRune

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.countRune.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.countRune.spec (GF := GF) (hG := hG) := by
  intro str x
  wp_start
  wp_auto
  wp_apply (wp_string_for_range str _ (fun i => iprop(
      n_ptr ↦ W64 ((((go.runes str).take i).countP (fun p => p.2 = x) : Nat) : Int) ∗
      x_ptr ↦ x ∗ ∃ rv : w32, r_ptr ↦ rv))) $$ [n x r]
  · simp only [List.take_zero, List.countP_nil]
    iframe
  · imodintro
    iintro %i %k %rv %hk ⟨Hn, Hx, ⟨%rv0, Hr⟩⟩
    have htake : (go.runes str).take (i + 1) = (go.runes str).take i ++ [(k, rv)] := by
      rw [List.take_add_one, hk]; rfl
    rw [htake, List.countP_append]
    generalize List.countP (fun p => decide (p.2 = x)) (List.take i (go.runes str)) = c
    wp_auto
    wp_if_destruct
    · rw [show List.countP (fun p => decide (p.2 = x)) [(k, rv)] = 1 by simp [Hif],
        show W64 ((c + 1 : Nat) : Int) = W64 (c : Int) + W64 1 by word]
      iapply forRangePostcondition_do
      iframe
    · rw [show List.countP (fun p => decide (p.2 = x)) [(k, rv)] = 0 by simp [Hif], Nat.add_zero]
      iapply forRangePostcondition_do
      iframe
  · iintro ⟨Hn, Hx, Hr⟩
    rw [List.take_length]
    wp_auto
    iapply HΦ
    iexact Hpre

end proof

end Perennial
