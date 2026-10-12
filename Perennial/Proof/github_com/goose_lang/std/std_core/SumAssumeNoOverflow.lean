/-
The proof of `github.com/goose-lang/std/std_core.SumAssumeNoOverflow`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.std_core.SumAssumeNoOverflow
public import Perennial.Spec.github_com.goose_lang.std.std_core.SumNoOverflow
public import Perennial.Spec.github_com.goose_lang.primitive.Assume

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

theorem github_com.goose_lang.std.std_core.SumAssumeNoOverflow.wp_proof
    (wp_SumNoOverflow : github_com.goose_lang.std.std_core.SumNoOverflow.spec (GF := GF) (hG := hG))
    (wp_Assume : github_com.goose_lang.primitive.Assume.spec (GF := GF) (hG := hG)) :
    github_com.goose_lang.std.std_core.SumAssumeNoOverflow.spec (GF := GF) (hG := hG) := fun x y => by
  wp_start
  wp_auto
  wp_apply wp_SumNoOverflow
  wp_apply wp_Assume as %Hassume
  iapply HΦ
  ipureintro
  simpa using Hassume

end proof

end Perennial
