/-
The proof of `unicode/utf8.RuneCountInString`.
-/
module

public import Perennial.Spec.unicode.utf8.RuneCountInString

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

theorem unicode.utf8.RuneCountInString.wp_proof :
    unicode.utf8.RuneCountInString.spec (GF := GF) (hG := hG) := by
  intro str
  wp_start
  wp_auto
  wp_apply (wp_string_for_range str _ (fun i => iprop(n_ptr ↦ W64 (i : Int)))) $$ [n]
  · rw [show W64 ((0 : Nat) : Int) = zero_val w64 from rfl]
    iexact n
  · imodintro
    iintro %i %k %rv %hk Hn
    wp_auto
    rw [show W64 ((i + 1 : Nat) : Int) = W64 (i : Int) + W64 1 by word]
    iapply forRangePostcondition_do
    iexact Hn
  · iintro Hn
    wp_auto
    iapply HΦ
    itrivial

end proof

end Perennial
