/-
The proof of `sync.(*Cond).Signal`.
-/
module

public import Perennial.Spec.sync.Cond__Signal
public import Perennial.Spec.sync.copyChecker__check
public import Perennial.Spec.sync.runtime_notifyListNotifyOne

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.Cond.Signal.wp_proof
    (wp_copyChecker_check : sync.copyChecker.check.spec (GF := GF) (hG := hG))
    (wp_runtime_notifyListNotifyOne : sync.runtime_notifyListNotifyOne.spec (GF := GF) (hG := hG)) :
    sync.Cond.Signal.spec (GF := GF) (hG := hG) := by
  intro c lk
  wp_start as H
  simp only [isCond_unseal, isCondDef]
  iNamed H
  wp_auto
  wp_apply wp_copyChecker_check $$ [$Hchecker]
  wp_apply wp_runtime_notifyListNotifyOne $$ [$Hnotify] with _
  wp_end

end proof

end Perennial
