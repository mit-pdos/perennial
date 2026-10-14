/-
The proof of `sync.(*Cond).Wait`.
-/
module

public import Perennial.Spec.sync.Cond__Wait
public import Perennial.Spec.sync.copyChecker__check
public import Perennial.Spec.sync.runtime_notifyListAdd
public import Perennial.Spec.sync.runtime_notifyListWait

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

theorem sync.Cond.Wait.wp_proof
    (wp_copyChecker_check : sync.copyChecker.check.spec (GF := GF) (hG := hG))
    (wp_runtime_notifyListAdd : sync.runtime_notifyListAdd.spec (GF := GF) (hG := hG))
    (wp_runtime_notifyListWait : sync.runtime_notifyListWait.spec (GF := GF) (hG := hG)) :
    sync.Cond.Wait.spec (GF := GF) (hG := hG) := fun c m R => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so it
  -- fails on a goal `R -∗ _` with `R` introduced by a tactic)
  wp_start as ⟨H, #Hlock, HR⟩
  simp only [isCond_unseal, isCondDef]
  iNamed H
  wp_auto
  wp_apply wp_copyChecker_check $$ [$Hchecker]
  wp_apply wp_runtime_notifyListAdd $$ [$Hnotify] with %x _
  unfold isLocker
  iNamed Hlock
  wp_apply H_Unlock $$ HR
  wp_apply wp_runtime_notifyListWait $$ [$Hnotify] with _
  wp_apply H_Lock $$ [] with HR
  wp_end

end proof

end Perennial
