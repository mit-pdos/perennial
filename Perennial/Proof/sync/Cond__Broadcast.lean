/-
The proof of `sync.(*Cond).Broadcast`.
-/
module

public import Perennial.Spec.sync.Cond__Broadcast
public import Perennial.Spec.sync.copyChecker__check
public import Perennial.Spec.sync.runtime_notifyListNotifyAll

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.Cond.Broadcast.wp_proof
    (wp_copyChecker_check : sync.copyChecker.check.spec (GF := GF) (hG := hG))
    (wp_runtime_notifyListNotifyAll : sync.runtime_notifyListNotifyAll.spec (GF := GF) (hG := hG)) :
    sync.Cond.Broadcast.spec (GF := GF) (hG := hG) := by
  intro c lk
  wp_start as H
  simp only [isCond_unseal, isCondDef]
  iNamed H
  wp_auto
  wp_apply wp_copyChecker_check $$ [$Hchecker]
  wp_apply wp_runtime_notifyListNotifyAll $$ [$Hnotify] with _
  wp_end

end proof

end Perennial
