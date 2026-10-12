/-
The proof of `github.com/goose-lang/std.newJoinHandle`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.newJoinHandle
public import Perennial.Spec.sync.NewCond

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

theorem github_com.goose_lang.std.newJoinHandle.wp_proof
    (wp_NewCond : sync.NewCond.spec (GF := GF) (hG := hG)) :
    github_com.goose_lang.std.newJoinHandle.spec (GF := GF) (hG := hG) := fun P => by
  wp_start
  wp_auto
  wp_apply wp_NewCond as %cond_l #Hcond
  wp_alloc jh_l as Hjh
  iStructNamed Hjh
  ipersist mu
  ipersist cond
  imod sync.init_Mutex (jhInv jh_l P) ⊤ «$r0_ptr» $$ «$r0» [done] with #Hlock
  · inext; iexists false; iframe; unfold jhP; simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  wp_auto
  iapply HΦ
  unfold isJoinHandle
  iexists «$r0_ptr», cond_l
  iframe #

end proof

end Perennial
