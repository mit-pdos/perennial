/-
The proof of `strconv.toError`.
-/
module

public import Perennial.Spec.strconv.toError
public import Perennial.Spec.strconv.syntaxError
public import Perennial.Spec.strconv.rangeError

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

theorem strconv.toError.wp_proof
    (wp_syntaxError : strconv.syntaxError.spec (GF := GF) (hG := hG))
    (wp_rangeError : strconv.rangeError.spec (GF := GF) (hG := hG)) :
    strconv.toError.spec (GF := GF) (hG := hG) := by
  intro fn s base bitSize syn
  wp_start
  wp_auto
  cases syn
  · rw [decide_eq_false (show ¬ W64 (if false = true then 2 else 1) = W64 2 by decide)]
    wp_auto
    wp_apply wp_rangeError as %l Hl
    iapply HΦ; simp only [Bool.false_eq_true, if_false, if_true]; iexact Hl
  · rw [decide_eq_true (show W64 (if true = true then 2 else 1) = W64 2 by decide)]
    wp_auto
    wp_apply wp_syntaxError as %l Hl
    iapply HΦ; simp only [Bool.false_eq_true, if_false, if_true]; iexact Hl

end proof

end Perennial
