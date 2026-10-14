/-
The proof of `github.com/goose-lang/std.Spawn`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.Spawn
public import Perennial.Spec.github_com.goose_lang.std.newJoinHandle
public import Perennial.Spec.github_com.goose_lang.std.JoinHandle__finish

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
variable [package_sem : github_com.goose_lang.std.Assumptions]

theorem github_com.goose_lang.std.Spawn.wp_proof
    (wp_newJoinHandle : github_com.goose_lang.std.newJoinHandle.spec (GF := GF) (hG := hG))
    (wp_JoinHandle_finish : github_com.goose_lang.std.JoinHandle.finish.spec (GF := GF) (hG := hG)) :
    github_com.goose_lang.std.Spawn.spec (GF := GF) (hG := hG) := fun P f => by
  wp_start as Hwp
  wp_auto
  wp_apply wp_newJoinHandle P as %l #Hhandle
  ipersist f
  ipersist h
  wp_bind (Fork _)
  iapply wp_fork $$ [Hwp] [-]
  · inext
    wp_auto
    wp_apply Hwp
    iintro HP
    wp_auto
    wp_apply wp_JoinHandle_finish $$ [$Hhandle $HP]
    itrivial
  · inext
    wp_auto
    iapply HΦ $$ Hhandle

end proof

end Perennial
