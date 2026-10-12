/-
The proof of `context.WithDeadlineCause`.
-/
module

public import Perennial.Spec.context.WithDeadlineCause
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.sync.atomic.Value__Load
public import Perennial.Spec.time.Time__Before
public import Perennial.Spec.time.Until
public import Perennial.Spec.time.AfterFunc
public import Perennial.Spec.context.cancelCtx__Done
public import Perennial.Spec.context.cancelCtx__Err
public import Perennial.Spec.context.cancelCtx__Value
public import Perennial.Spec.context.cancelCtx__cancel
public import Perennial.Spec.context.cancelCtx__propagateCancel
public import Perennial.Spec.context.withCancel_
public import Perennial.Spec.context.timerCtx__cancel
public import Perennial.Proof.context.CancelCtxCells
public import Perennial.Proof.context.TimerCtx
public import Perennial.Proof.context.PropagateCancel
public import Perennial.Proof.context.WithCancelGen
public import Perennial.Proof.time.PtrMethods

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.WithDeadlineCause.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (wp_Before : time.Time.Before.spec (GF := GF) (hG := hG))
    (wp_Until : time.Until.spec (GF := GF) (hG := hG))
    (wp_AfterFunc : time.AfterFunc.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (wp_withCancel : context.withCancel.spec (GF := GF) (hG := hG))
    (wp_timerCtx_cancel : context.timerCtx.cancel.spec (GF := GF) (hG := hG)) :
    context.WithDeadlineCause.spec (GF := GF) (hG := hG) := fun parent parent_desc d cause => by
  have wp_err_Load := wp_err_Load_of wp_VLoad
  have childCancelSpec_timerCtx := childCancelSpec_timerCtx_of wp_timerCtx_cancel
  have isContext_timerCtx := isContext_timerCtx_of wp_cancelCtx_Done wp_cancelCtx_Err
      wp_cancelCtx_Value wp_VLoad
  have wp_WithCancel_any := wp_WithCancel_any_of wp_withCancel wp_cancelCtx_cancel
      wp_propagateCancel wp_cancelCtx_Done wp_cancelCtx_Err wp_cancelCtx_Value wp_VLoad
  have wp_propagateCancel_any := wp_propagateCancel_any_of wp_propagateCancel
  have wp_ptr_Before := time.Time.wp_ptr_Before_of wp_Before
  wp_start as #Hctx
  ihave #Hctx2 := Hctx
  iunfold isContext at Hctx2
  iunfold isContextDef at Hctx2
  icases Hctx2 with ⟨#HDeadline, -, -, -, -, -, -, #Hcci⟩
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, _, ⟨%canceled, #Hcanceled, %hcanceled⟩, ⟨%dexc, #Hdexc, %hdexc⟩, _⟩
  wp_auto
  iapply wp_with_defer
  iintro %defer Hdefer
  wp_auto
  wp_apply HDeadline
  cases hdl : parent_desc.Deadline with
  | some cur =>
    dsimp only [Option.getD]
    wp_auto
    wp_apply wp_Before as %b -
    cases b
    case true =>
      wp_auto
      wp_apply wp_WithCancel_any parent parent_desc $$ [$Hctx]
        as %ctx' %γ' %cancel ⟨#Hcancel, #Hctx'⟩
      have heq : ({ parent_desc with PDone := iprop(True), Done_gn := γ' } : ContextDesc (IProp GF)) =
          { parent_desc with Deadline := some cur, PDone := iprop(True), Done_gn := γ' } := by
        cases parent_desc; simp only at hdl; subst hdl; rfl
      rw [heq] at *
      iapply HΦ $$ %ctx' %γ' %cancel %cur
      isplitl []
      · ipureintro; right; rfl
      isplitl []
      · unfold cancelSpec
        imodintro
        iintro %Φ' - HΦ'
        iapply Hcancel
        · imodintro; itrivial
        inext; iintro -; iapply HΦ' $$ []; itrivial
      · iexact Hctx'
    all_goals
      wp_auto
      iStructNamedPrefix «$r0» "T"
      ipersist c
      ipersist cause
      ihave HtR : timerR «$r0_ptr» $$ [Ttimer]
      · unfold timerR; iexists _; iframe; ileft; ipureintro; rfl
      imod cancelCtx_alloc (tcc «$r0_ptr») iprop(True) (timerR «$r0_ptr») $$ Hcci TcancelCtx HtR
        with ⟨%γ, #Hc, Hf⟩
      ipersist Tdeadline
      ihave #Hk := childCancelSpec_timerCtx «$r0_ptr» γ $$ [$Hpkg $Hc]
      wp_apply wp_propagateCancel_any (tcc «$r0_ptr») parent parent_desc _ $$ [$Hf $Hctx $Hk] as Hf
      ipersist Hf
      ihave #Hc' := isCancelCtxOfR_of _ _ _ _ $$ Hc
      wp_apply wp_Until as %dur -
      wp_if_destruct
      · wp_apply wp_timerCtx_cancel «$r0_ptr» γ true dexc cause hdexc $$ [$Hc] as -
        · simp only [↓reduceIte]
          iexists parent; iframe #
          unfold isParentCtx; iright; iexists parent_desc; iframe #
        iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.timerCtx.ty) #«$r0_ptr») %γ
        isplitl []
        · ipureintro; left; rfl
        isplitl []
        · imodintro
          iintro %Φ' - HΦ'
          wp_auto
          wp_apply wp_timerCtx_cancel «$r0_ptr» γ false canceled GoInterface.nil hcanceled $$ [$Hc]
            as -
          · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
          iapply HΦ' $$ []; itrivial
        · iapply isContext_timerCtx «$r0_ptr» γ d _ rfl rfl rfl
          iframe #
      · ihave #Hc2 := Hc
        iunfold isCancelCtxOfR at Hc2
        icases Hc2 with ⟨#Hmu, -, -⟩
        wp_apply wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
        iunfold cancelCtxLockInv at Hlk
        icases Hlk with ⟨%children, %cause0, %od, %closed, Hchildren, Hcause, Hcl, Hod, HR⟩
        iunfold timerR at HR
        icases HR with ⟨%tm0, Htm0, Htm0r⟩
        wp_apply wp_err_Load (tcc «$r0_ptr») γ iprop(True) false $$ [$Hc'] as %e ⟨-, -⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
        cases e with
        | nil =>
          wp_auto
          wp_apply wp_AfterFunc as %tm #Htm
          · wp_auto
            wp_apply wp_timerCtx_cancel «$r0_ptr» γ true dexc cause hdexc $$ [$Hc] as -
            · simp only [↓reduceIte]
              iexists parent; iframe #
              unfold isParentCtx; iright; iexists parent_desc; iframe #
            itrivial
          wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hod Htm0]
          · inext; unfold cancelCtxLockInv; iexists children, cause0, od, closed; iframe
            unfold timerR; iexists tm; iframe; iright; iexact Htm
          iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.timerCtx.ty) #«$r0_ptr») %γ
          isplitl []
          · ipureintro; left; rfl
          isplitl []
          · imodintro
            iintro %Φ' - HΦ'
            wp_auto
            wp_apply wp_timerCtx_cancel «$r0_ptr» γ true canceled GoInterface.nil hcanceled $$ [$Hc]
              as -
            · simp only [↓reduceIte]
              iexists parent; iframe #
              unfold isParentCtx; iright; iexists parent_desc; iframe #
            iapply HΦ' $$ []; itrivial
          · iapply isContext_timerCtx «$r0_ptr» γ d _ rfl rfl rfl
            iframe #
        | ok ie =>
          wp_auto
          wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hod Htm0 Htm0r]
          · inext; unfold cancelCtxLockInv; iexists children, cause0, od, closed; iframe
            unfold timerR; iexists tm0; iframe
          iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.timerCtx.ty) #«$r0_ptr») %γ
          isplitl []
          · ipureintro; left; rfl
          isplitl []
          · imodintro
            iintro %Φ' - HΦ'
            wp_auto
            wp_apply wp_timerCtx_cancel «$r0_ptr» γ true canceled GoInterface.nil hcanceled $$ [$Hc]
              as -
            · simp only [↓reduceIte]
              iexists parent; iframe #
              unfold isParentCtx; iright; iexists parent_desc; iframe #
            iapply HΦ' $$ []; itrivial
          · iapply isContext_timerCtx «$r0_ptr» γ d _ rfl rfl rfl
            iframe #
  | none =>
    dsimp only [Option.getD]
    wp_auto
    iStructNamedPrefix «$r0» "T"
    ipersist c
    ipersist cause
    ihave HtR : timerR «$r0_ptr» $$ [Ttimer]
    · unfold timerR; iexists _; iframe; ileft; ipureintro; rfl
    imod cancelCtx_alloc (tcc «$r0_ptr») iprop(True) (timerR «$r0_ptr») $$ Hcci TcancelCtx HtR
      with ⟨%γ, #Hc, Hf⟩
    ipersist Tdeadline
    ihave #Hk := childCancelSpec_timerCtx «$r0_ptr» γ $$ [$Hpkg $Hc]
    wp_apply wp_propagateCancel_any (tcc «$r0_ptr») parent parent_desc _ $$ [$Hf $Hctx $Hk] as Hf
    ipersist Hf
    ihave #Hc' := isCancelCtxOfR_of _ _ _ _ $$ Hc
    wp_apply wp_Until as %dur -
    wp_if_destruct
    · wp_apply wp_timerCtx_cancel «$r0_ptr» γ true dexc cause hdexc $$ [$Hc] as -
      · simp only [↓reduceIte]
        iexists parent; iframe #
        unfold isParentCtx; iright; iexists parent_desc; iframe #
      iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.timerCtx.ty) #«$r0_ptr») %γ
      isplitl []
      · ipureintro; left; rfl
      isplitl []
      · imodintro
        iintro %Φ' - HΦ'
        wp_auto
        wp_apply wp_timerCtx_cancel «$r0_ptr» γ false canceled GoInterface.nil hcanceled $$ [$Hc]
          as -
        · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
        iapply HΦ' $$ []; itrivial
      · iapply isContext_timerCtx «$r0_ptr» γ d _ rfl rfl rfl
        iframe #
    · ihave #Hc2 := Hc
      iunfold isCancelCtxOfR at Hc2
      icases Hc2 with ⟨#Hmu, -, -⟩
      wp_apply wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
      iunfold cancelCtxLockInv at Hlk
      icases Hlk with ⟨%children, %cause0, %od, %closed, Hchildren, Hcause, Hcl, Hod, HR⟩
      iunfold timerR at HR
      icases HR with ⟨%tm0, Htm0, Htm0r⟩
      wp_apply wp_err_Load (tcc «$r0_ptr») γ iprop(True) false $$ [$Hc'] as %e ⟨-, -⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      cases e with
      | nil =>
        wp_auto
        wp_apply wp_AfterFunc as %tm #Htm
        · wp_auto
          wp_apply wp_timerCtx_cancel «$r0_ptr» γ true dexc cause hdexc $$ [$Hc] as -
          · simp only [↓reduceIte]
            iexists parent; iframe #
            unfold isParentCtx; iright; iexists parent_desc; iframe #
          itrivial
        wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hod Htm0]
        · inext; unfold cancelCtxLockInv; iexists children, cause0, od, closed; iframe
          unfold timerR; iexists tm; iframe; iright; iexact Htm
        iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.timerCtx.ty) #«$r0_ptr») %γ
        isplitl []
        · ipureintro; left; rfl
        isplitl []
        · imodintro
          iintro %Φ' - HΦ'
          wp_auto
          wp_apply wp_timerCtx_cancel «$r0_ptr» γ true canceled GoInterface.nil hcanceled $$ [$Hc]
            as -
          · simp only [↓reduceIte]
            iexists parent; iframe #
            unfold isParentCtx; iright; iexists parent_desc; iframe #
          iapply HΦ' $$ []; itrivial
        · iapply isContext_timerCtx «$r0_ptr» γ d _ rfl rfl rfl
          iframe #
      | ok ie =>
        wp_auto
        wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hod Htm0 Htm0r]
        · inext; unfold cancelCtxLockInv; iexists children, cause0, od, closed; iframe
          unfold timerR; iexists tm0; iframe
        iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.timerCtx.ty) #«$r0_ptr») %γ
        isplitl []
        · ipureintro; left; rfl
        isplitl []
        · imodintro
          iintro %Φ' - HΦ'
          wp_auto
          wp_apply wp_timerCtx_cancel «$r0_ptr» γ true canceled GoInterface.nil hcanceled $$ [$Hc]
            as -
          · simp only [↓reduceIte]
            iexists parent; iframe #
            unfold isParentCtx; iright; iexists parent_desc; iframe #
          iapply HΦ' $$ []; itrivial
        · iapply isContext_timerCtx «$r0_ptr» γ d _ rfl rfl rfl
          iframe #

end proof

end Perennial
