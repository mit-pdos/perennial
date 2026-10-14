/-
The proof of `context.(*timerCtx).cancel`.
-/
module

public import Perennial.Spec.context.timerCtx__cancel
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.time.Timer__Stop
public import Perennial.Spec.context.cancelCtx__cancel
public import Perennial.Spec.context.removeChild
public import Perennial.Proof.context.TimerCtx

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.timerCtx.cancel.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_Stop : time.Timer.Stop.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (wp_removeChild : context.removeChild.spec (GF := GF) (hG := hG)) :
    context.timerCtx.cancel.spec (GF := GF) (hG := hG) := fun c γ rm err cause herr => by
  have wp_Stop_func := wp_Timer_Stop_func_of wp_Stop
  wp_start as ⟨#Hc, Hrm⟩
  ihave #Hc' := isCancelCtxOfR_of _ _ _ _ $$ Hc
  wp_auto
  wp_apply wp_cancelCtx_cancel (tcc c) γ iprop(True) false err cause herr $$ [$Hc'] as #Hclosed
  · isplitl []
    · imodintro; itrivial
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  iunfold isCancelCtxOfR at Hc
  iNamed Hc
  cases rm
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  rotate_left
  icases Hrm with ⟨%parent, #Hpf, #Hpar⟩
  wp_auto
  wp_apply wp_removeChild parent
    (interface.mkOk (go.GoType.PointerType context.timerCtx.ty) #c) $$ [$Hpar]
  all_goals
    try wp_auto
    wp_apply wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
    iunfold cancelCtxLockInv at Hlk
    icases Hlk with ⟨%children, %cause0, %od, %closed, Hchildren, Hcause, Hcl, Hod, HR⟩
    iunfold timerR at HR
    icases HR with ⟨%tm, Htm, Htmr⟩
    wp_auto
    by_cases htm : tm = Loc.null
    · subst htm
      wp_auto
      wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hod Htm]
      · inext; unfold cancelCtxLockInv; iexists children, cause0, od, closed; iframe
        unfold timerR; iexists Loc.null; iframe; ileft; ipureintro; rfl
      iapply HΦ $$ Hclosed
    · icases Htmr with (%h | #Htf)
      · exact absurd h htm
      rw [decide_eq_false htm]
      wp_auto
      wp_apply wp_Stop_func tm $$ [$Htf] as %b -
      wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hod Htm]
      · inext; unfold cancelCtxLockInv; iexists children, cause0, od, closed; iframe
        unfold timerR; iexists Loc.null; iframe; ileft; ipureintro; rfl
      iapply HΦ $$ Hclosed

end proof

end Perennial
