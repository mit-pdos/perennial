/-
A `*timerCtx` (the context of `WithDeadlineCause`): the specs of its `Done`, `Err` and `Value`
methods (promoted from the embedded `cancelCtx`: method-set wrappers, from the `*cancelCtx`
specs), its `childCancelSpec`, `parentCancelCtx(c)` for a `*timerCtx` `c`
(`wp_parentCancelCtx_timer_of`: a second triple of `parentCancelCtx`, with the exact result,
proved from its code), and `isContext_timerCtx_of`; and `wp_Timer_Stop_func_of`, the
`AfterFunc` case of `time.Timer.Stop.spec`. The specs they use are hypotheses; `Results.lean`
has them under their old names, without them.
-/
module

public import Perennial.Proof.context.CancelCtxCells
public import Perennial.Spec.context.cancelCtx__Done
public import Perennial.Spec.context.cancelCtx__Err
public import Perennial.Spec.context.cancelCtx__Value
public import Perennial.Spec.context.timerCtx__cancel
public import Perennial.Spec.time.Timer__Stop

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace context

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

open ContextDesc

/-! ### `*timerCtx` -/

theorem wp_timerCtx_Done_of
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf (tcc c) γ P }}
      (App (Val #(methods (go.GoType.PointerType context.timerCtx.ty) go!"Done" #c)) (Val #()))
    {{ (ch : GoChan) (γch : ChanNames), RET #ch; isContextDone (cdesc γ P) ch γch ∗
        doneFresh γ P ch }} := by
  wp_start as #Hc
  wp_apply wp_cancelCtx_Done (tcc c) γ P $$ [$Hc] as %ch %γch ⟨#Hd, #Hfr⟩
  iapply HΦ; iframe #

theorem wp_timerCtx_Err_of
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P : IProp GF) (cl : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf (tcc c) γ P ∗
        (if cl then ContextClosed γ else iprop(True)) }}
      (App (Val #(methods (go.GoType.PointerType context.timerCtx.ty) go!"Err" #c)) (Val #()))
    {{ (e : GoInterface), RET #e; ⌜cl = true → e ≠ interface.nil⌝ ∗
        (if e = interface.nil then iprop(True)
         else iprop(⌜isTypedErr e⌝ ∗ □ P ∗ ContextClosed γ)) }} := by
  wp_start as ⟨#Hc, Hcl⟩
  wp_apply wp_cancelCtx_Err (tcc c) γ P cl $$ [$Hc $Hcl] as %e He
  iapply HΦ $$ He

theorem wp_timerCtx_Value_of
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf (tcc c) γ P }}
      (App (Val #(methods (go.GoType.PointerType context.timerCtx.ty) go!"Value" #c))
        (Val #cancelCtxKeyAny))
    {{ RET #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #(tcc c)); True }} := by
  wp_start as #Hc
  wp_apply wp_cancelCtx_Value (tcc c) γ P $$ [$Hc]
  iapply HΦ; itrivial

/-- The `childCancelSpec` of a `*timerCtx` (it needs nothing of its parent's Done
proposition). -/
theorem childCancelSpec_timerCtx_of
    (wp_timerCtx_cancel : context.timerCtx.cancel.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
        isCancelCtxOfR (tcc c) γ iprop(True) (timerR c) ⊢
      childCancelSpec iprop(True)
        (interface.mkOk (go.GoType.PointerType context.timerCtx.ty) #c) := by
  iintro ⟨#Hpkg, #Hc⟩
  simp only [childCancelSpec]
  imodintro
  iintro %err %cause %Φ %herr - HΦ
  iapply wp_timerCtx_cancel c γ false err cause herr $$ [$Hpkg $Hc]
  · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  inext; iintro -; iexact HΦ

/-- `parentCancelCtx(c)` for a `*timerCtx` `c` whose Done channel `ch` is not `closedchan`: it
returns the embedded `*cancelCtx`. -/
theorem wp_parentCancelCtx_timer_of
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P : IProp GF) (ch cch : GoChan)
    (hcch : ch ≠ cch) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf (tcc c) γ P ∗
        dghostVar γ.doneGn .discard (some ch) ∗ globalAddr context.closedchan ↦□ cch }}
      (App (Val (@! context.parentCancelCtx))
        (Val #(interface.ok (interface.mk (go.GoType.PointerType context.timerCtx.ty) #c))))
    {{ RET (PairV #(tcc c) #true); True }} := by
  have wp_done_Load_known := wp_done_Load_known_of wp_VLoad
  have wp_timerCtx_Done := wp_timerCtx_Done_of wp_cancelCtx_Done
  have wp_timerCtx_Value := wp_timerCtx_Value_of wp_cancelCtx_Value
  wp_start as ⟨#Hp, #Hd, #Hcch⟩
  wp_alloc par as Hpar
  wp_pures
  wp_load
  wp_pures
  wp_apply wp_timerCtx_Done c _ _ $$ [$Hp] as %ch' %γch' ⟨#Hd', -⟩
  ihave #Hdd' := isContextDone_doneGn _ _ _ $$ Hd'
  ihave %heq := dghostVar_agree _ _ _ _ _ $$ Hd Hdd'
  cases heq
  ihave #Hch := isContextDone_is_chan _ _ _ $$ Hd'
  ihave %hnn := isChan_ne_nil _ _ $$ Hch
  rw [decide_eq_false hcch]
  wp_auto
  rw [decide_eq_false hnn]
  wp_auto
  wp_apply wp_timerCtx_Value c _ _ $$ [$Hp]
  wp_apply wp_done_Load_known (tcc c) _ _ ch $$ [$Hp $Hd]
  iapply HΦ; itrivial

/-- A `*timerCtx` `c` (names `γ`, Done proposition `True`) with deadline `d` is a context
described by `s` (whose deadline is `some d`). -/
theorem isContext_timerCtx_of
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (d : time.Time)
    (s : ContextDesc (IProp GF)) (hγ : s.Done_gn = γ) (hP : s.PDone = iprop(True))
    (hd : s.Deadline = some d) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
        isCancelCtxOfR (tcc c) γ iprop(True) (timerR c) ∗
        structFieldRef context.timerCtx go!"deadline" c ↦□ d ⊢
      isContext (interface.mk (go.GoType.PointerType context.timerCtx.ty) #c) s := by
  have wp_parentCancelCtx_timer := wp_parentCancelCtx_timer_of wp_cancelCtx_Done wp_cancelCtx_Value
      wp_VLoad
  have wp_timerCtx_Done := wp_timerCtx_Done_of wp_cancelCtx_Done
  have wp_timerCtx_Err := wp_timerCtx_Err_of wp_cancelCtx_Err
  have wp_timerCtx_Value := wp_timerCtx_Value_of wp_cancelCtx_Value
  iintro ⟨#Hpkg, #HcR, #Hdl⟩
  ihave #Hc := isCancelCtxOfR_of _ _ _ _ $$ HcR
  subst hγ
  unfold isContext isContextDef
  isplitl []
  · imodintro
    iintro %Φ - HΦ
    wp_method_call
    wp_auto
    rw [hd]
    dsimp only [Option.getD]
    iapply HΦ $$ []
    itrivial
  isplitl []
  · imodintro
    iintro %Φ - HΦ
    iapply wp_timerCtx_Done $$ [$Hpkg $Hc]
    inext
    iintro %ch %γch ⟨#Hd, -⟩
    iapply HΦ
    iapply isContextDone_congr $$ Hd
    · unfold cdesc; simp
    · unfold cdesc; simp [hP]
  isplitl []
  · iintro %cl
    imodintro
    iintro %Φ Hpre HΦ
    cases cl
    case Done =>
      iapply wp_timerCtx_Err c _ _ true $$ [$Hpkg $Hc Hpre]
      · simp only [↓reduceIte]; iexact Hpre
      inext
      iintro %e ⟨%hne, -⟩
      iapply HΦ
      ipureintro; exact hne rfl
    all_goals
      iapply wp_timerCtx_Err c _ _ false $$ [$Hpkg $Hc]
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      inext
      iintro %e ⟨-, He⟩
      iapply HΦ
      dsimp only
      by_cases he : e = interface.nil
      · subst he; simp only [ite_true]; itrivial
      · rw [ite_eq_right he]; rw [ite_eq_right he] at *
        icases He with ⟨-, -, #Hcl⟩
        rw [hP]
        isplitl []
        · imodintro; itrivial
        · iexact Hcl
  isplitl []
  · imodintro
    iintro %Φ - HΦ
    iapply wp_timerCtx_Value $$ [$Hpkg $Hc]
    inext
    iintro -
    iapply HΦ
    simp only [isCancelCtxAny, ↓reduceIte]
    iexists (tcc c)
    isplitl []
    · ipureintro; rfl
    · unfold isCancelCtx; iexists s.Done_gn, iprop(True); iexact Hc
  isplitl []
  · imodintro
    iintro %Φ #Hcl HΦ
    iapply wp_timerCtx_Err c _ _ true $$ [$Hpkg $Hc]
    · simp only [↓reduceIte]; iexact Hcl
    inext
    iintro %e ⟨%hne, He⟩
    have hne := hne rfl
    rw [ite_eq_right hne]
    icases He with ⟨%ht, -⟩
    iapply HΦ; ipureintro; exact ht
  isplitl []
  · imodintro
    iintro %ch #Hd
    iapply cancelCtx_doneFresh $$ Hc Hd
  isplitl []
  · isplitl []
    · ipureintro; exact timerCtx_ne_stopCtx
    · imodintro
      iintro %ch %cch %Φ #Hd #Hcch %hne HΦ
      iapply wp_parentCancelCtx_timer c _ _ ch cch hne $$ [$Hpkg $Hc $Hd $Hcch]
      inext; iintro -
      iapply HΦ
      unfold isCancelCtx; iexists _, _; iexact Hc
  · iapply isCancelCtxOf_closedchan $$ Hc

/-- `(*Timer).Stop()` for a timer made by `AfterFunc` (`isFuncTimer`): some `bool` (the second case
of `time.Timer.Stop.spec`; `time.Timer.wp_Stop_func` in `time`'s `Results`). -/
theorem wp_Timer_Stop_func_of (wp_Stop : time.Timer.Stop.spec (GF := GF) (hG := hG)) (t : Loc) :
    {{ time.isFuncTimer (GF := GF) t }}
      (App (Val (t @!! go.GoType.PointerType time.Timer.ty @!! go!"Stop")) (Val #()))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ #Ht HΦ
  wp_apply wp_Stop t $$ [] as %b -
  · iright; iexact Ht
  iapply HΦ
  itrivial

end wps

end context

end Perennial
