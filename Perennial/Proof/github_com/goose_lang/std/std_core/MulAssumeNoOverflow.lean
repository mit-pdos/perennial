/-
The proof of `github.com/goose-lang/std/std_core.MulAssumeNoOverflow`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.std_core.MulAssumeNoOverflow
public import Perennial.Spec.github_com.goose_lang.std.std_core.MulNoOverflow
public import Perennial.Spec.github_com.goose_lang.primitive.Assume

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.std.std_core.Assumptions]

theorem github_com.goose_lang.std.std_core.MulAssumeNoOverflow.wp_proof
    (wp_MulNoOverflow : github_com.goose_lang.std.std_core.MulNoOverflow.spec (GF := GF) (hG := hG))
    (wp_Assume : github_com.goose_lang.primitive.Assume.spec (GF := GF) (hG := hG)) :
    github_com.goose_lang.std.std_core.MulAssumeNoOverflow.spec (GF := GF) (hG := hG) := fun x y => by
  wp_start
  wp_auto
  wp_apply wp_MulNoOverflow
  wp_apply wp_Assume as %Hassume
  iapply HΦ
  ipureintro
  simpa using Hassume

end proof

end Perennial
