/-
The proof of `github.com/goose-lang/std/std_core.SumNoOverflow`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.std_core.SumNoOverflow

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.std.std_core.Assumptions]

theorem github_com.goose_lang.std.std_core.SumNoOverflow.wp_proof :
    github_com.goose_lang.std.std_core.SumNoOverflow.spec (GF := GF) (hG := hG) := fun x y => by
  wp_start as _
  wp_auto
  have h : (uint.Z x ≤ uint.Z (x + y)) ↔ (uint.Z (x + y) = uint.Z x + uint.Z y) := by
    have := sum_overflow_check x y
    constructor <;> intro <;> word
  rw [decide_eq_decide.mpr h]
  iapply HΦ
  itrivial

end proof

end Perennial
