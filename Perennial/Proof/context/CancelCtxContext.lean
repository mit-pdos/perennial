/-
A `*cancelCtx` is a context: `isContext_cancelCtx_of` (from the specs of its methods), its
`childCancelSpec` (`childCancelSpec_cancelCtx_of`), its `Err()` and `cancel` for unknown or any
allowed errors (`wp_cancelCtx_Err_any_of`, `wp_cancelCtx_cancel_any_of`), and `parentCancelCtx(c)` for a `*cancelCtx`
`c` (`wp_parentCancelCtx_self_of`: a second triple of `parentCancelCtx`, with the exact result,
proved from its code, for `isContext`'s `"#HParentCC"`). The specs they use are hypotheses;
`Results.lean` has them under their old names, without them.
-/
module

public import Perennial.Proof.context.CancelCtxCells
public import Perennial.Spec.context.cancelCtx__Done
public import Perennial.Spec.context.cancelCtx__Err
public import Perennial.Spec.context.cancelCtx__Value
public import Perennial.Spec.context.cancelCtx__cancel

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace context

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

open ContextDesc

/-- `parentCancelCtx(p)` for a `*cancelCtx` `p` whose Done channel `ch` (once determined, e.g.
by an earlier `p.Done()`) is not `closedchan`: it returns `p`. -/
theorem wp_parentCancelCtx_self_of
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (p : Loc) (γ : ContextNames) (P : IProp GF) (ch cch : GoChan)
    (hcch : ch ≠ cch) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf p γ P ∗
        dghostVar γ.doneGn .discard (some ch) ∗ globalAddr context.closedchan ↦□ cch }}
      (App (Val (@! context.parentCancelCtx))
        (Val #(interface.ok (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p))))
    {{ RET (PairV #p #true); True }} := by
  have wp_done_Load_known := wp_done_Load_known_of wp_VLoad
  wp_start as ⟨#Hp, #Hd, #Hcch⟩
  wp_auto
  wp_apply wp_cancelCtx_Done p _ _ $$ [$Hp] as %ch' %γch' ⟨#Hd', -⟩
  ihave #Hdd' := isContextDone_doneGn _ _ _ $$ Hd'
  ihave %heq := dghostVar_agree _ _ _ _ _ $$ Hd Hdd'
  cases heq
  ihave #Hch := isContextDone_is_chan _ _ _ $$ Hd'
  ihave %hnn := isChan_ne_nil _ _ $$ Hch
  rw [decide_eq_false hcch]
  wp_auto
  rw [decide_eq_false hnn]
  wp_auto
  wp_apply wp_cancelCtx_Value p _ _ $$ [$Hp]
  wp_apply wp_done_Load_known p _ _ ch $$ [$Hp $Hd]
  iapply HΦ; itrivial

/-- `c.Err()` for a `*cancelCtx` whose allowed errors are not known (`isCancelCtxOf`):
`context.cancelCtx.Err.spec` without what it says of them. -/
theorem wp_cancelCtx_Err_any_of
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P : IProp GF) (cl : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        (if cl then ContextClosed γ else iprop(True)) }}
      (App (Val #(methods (go.GoType.PointerType context.cancelCtx.ty) go!"Err" #c)) (Val #()))
    {{ (e : GoInterface), RET #e; ⌜cl = true → e ≠ interface.nil⌝ ∗
        (if e = interface.nil then iprop(True)
         else iprop(⌜isTypedErr e⌝ ∗ isCtxErr e ∗ □ P ∗ ContextClosed γ)) }} := by
  iintro %Φ ⟨#Hpkg, #Hc, Hcl⟩ HΦ
  icases isCancelCtxOf_A _ _ _ $$ Hc with ⟨%A, #HcA⟩
  iapply wp_cancelCtx_Err c γ P A cl $$ [$Hpkg $HcA $Hcl]
  inext
  iintro %e ⟨%hcl, He⟩
  iapply HΦ
  isplitl []
  · ipureintro; exact hcl
  by_cases he : e = interface.nil
  · subst he
    iclear He
    rw [ite_eq_left rfl]
    itrivial
  · simp only [he, ↓reduceIte]
    icases He with ⟨%ht, #Hce, #Hp, #Hcl', -⟩
    isplitl []; · ipureintro; exact ht
    isplitl []; · iexact Hce
    isplitl []; · imodintro; iexact Hp
    iexact Hcl'

/-- `c.cancel(rm, err, cause)` for a `*cancelCtx` that any context error may cancel
(`isCancelCtxOfA c γ P (fun _ => True)`): `context.cancelCtx.cancel.spec` with nothing to show of
`err` but that it is a typed context error. -/
theorem wp_cancelCtx_cancel_any_of
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P : IProp GF) (rm : Bool) (err cause : GoInterface)
    (herr : isTypedErr err) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOfA c γ P (fun _ => True) ∗
        isCtxErr err ∗ □ P ∗
        (if rm then iprop(∃ parent : GoInterfaceOk,
            structFieldRef context.cancelCtx go!"Context" c ↦□ (interface.ok parent : GoInterface) ∗
            isParentCtx parent)
         else iprop(True)) }}
      (App (App (App (Val #(methods (go.GoType.PointerType context.cancelCtx.ty) go!"cancel" #c))
        (Val #rm)) (Val #err)) (Val #cause))
    {{ RET #(); ContextClosed γ }} :=
  wp_cancelCtx_cancel c γ P (fun _ => True) rm err cause herr trivial

/-- The `childCancelSpec` of a `*cancelCtx` child whose Done proposition follows from the
parent's. -/
theorem childCancelSpec_cancelCtx_of
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P Q : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOfA c γ P (fun _ => True) ∗
        □ (Q -∗ P) ⊢
      childCancelSpec Q (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) := by
  have wp_cancelCtx_cancel := wp_cancelCtx_cancel_any_of wp_cancelCtx_cancel
  iintro ⟨#Hpkg, #Hc, #HQ⟩
  simp only [childCancelSpec]
  imodintro
  iintro %err %cause %Φ %herr #Hce #Hq HΦ
  iapply wp_cancelCtx_cancel c γ P false err cause herr $$ [$Hpkg $Hc $Hce]
  · isplitl []
    · imodintro; iapply HQ $$ Hq
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  inext; iintro -; iexact HΦ

/-- A `*cancelCtx` `c` (names `γ`, Done proposition `P`) whose parent has the deadline
`s.Deadline` is a context described by `s`. -/
theorem isContext_cancelCtx_of
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P : IProp GF) (parent : GoInterfaceOk)
    (s : ContextDesc (IProp GF)) (hγ : s.Done_gn = γ) (hP : s.PDone = P) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        ctxField c ↦□ (interface.ok parent : GoInterface) ∗ deadlineSpec parent s.Deadline ⊢
      isContext (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c) s := by
  have wp_parentCancelCtx_self := wp_parentCancelCtx_self_of wp_cancelCtx_Done wp_cancelCtx_Value
      wp_VLoad
  have wp_cancelCtx_Err := wp_cancelCtx_Err_any_of wp_cancelCtx_Err
  iintro ⟨#Hpkg, #Hc, #Hf, #Hdl⟩
  unfold isContext isContextDef
  isplitl []
  · imodintro
    iintro %Φ - HΦ
    wp_method_call
    wp_auto
    unfold deadlineSpec
    iapply Hdl
    · itrivial
    iexact HΦ
  isplitl []
  · imodintro
    iintro %Φ - HΦ
    iapply wp_cancelCtx_Done $$ [$Hpkg $Hc]
    inext
    iintro %ch %γch ⟨#Hd, -⟩
    iapply HΦ
    iapply isContextDone_congr $$ Hd
    · unfold cdesc; simp [hγ]
    · unfold cdesc; simp [hP]
  isplitl []
  · iintro %cl
    imodintro
    iintro %Φ Hpre HΦ
    subst hγ hP
    dsimp only
    cases cl
    case Done =>
      iapply wp_cancelCtx_Err c _ _ true $$ [$Hpkg $Hc Hpre]
      · simp only [↓reduceIte]; iexact Hpre
      inext
      iintro %e ⟨%hne, He⟩
      have hne := hne rfl
      rw [ite_eq_right hne] at *
      icases He with ⟨-, #Hce, -⟩
      iapply HΦ
      · ipureintro; exact hne
      · rw [ite_eq_right hne]; iexact Hce
    all_goals
      iapply wp_cancelCtx_Err c _ _ false $$ [$Hpkg $Hc]
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      inext
      iintro %e ⟨-, He⟩
      by_cases he : e = interface.nil
      · subst he
        iapply HΦ
        · dsimp only; simp only [ite_true]; itrivial
        · simp only [ite_true]; itrivial
      · rw [ite_eq_right he] at *
        icases He with ⟨-, #Hce, #Hp, #Hcl⟩
        iapply HΦ
        · dsimp only; rw [ite_eq_right he]; iframe #
        · rw [ite_eq_right he]; iexact Hce
  isplitl []
  · imodintro
    iintro %Φ - HΦ
    iapply wp_cancelCtx_Value $$ [$Hpkg $Hc]
    inext
    iintro -
    iapply HΦ
    simp only [isCancelCtxAny, ↓reduceIte]
    iexists c
    isplitl []
    · ipureintro; rfl
    · unfold isCancelCtx; iexists γ, P; iexact Hc
  subst hγ hP
  isplitl []
  · imodintro
    iintro %Φ #Hcl HΦ
    iapply wp_cancelCtx_Err c _ _ true $$ [$Hpkg $Hc]
    · simp only [↓reduceIte]; iexact Hcl
    inext
    iintro %e ⟨%hne, He⟩
    have hne := hne rfl
    rw [ite_eq_right hne]
    icases He with ⟨%ht, #Hce, #Hp, -⟩
    iapply HΦ
    · ipureintro; exact ht
    · iexact Hce
    · iexact Hp
  isplitl []
  · imodintro
    iintro %ch #Hd
    iapply cancelCtx_doneFresh $$ Hc Hd
  isplitl []
  · isplitl []
    · ipureintro; exact ptrCancelCtx_ne_stopCtx
    · imodintro
      iintro %ch %cch %Φ #Hd #Hcch %hne HΦ
      iapply wp_parentCancelCtx_self c _ _ ch cch hne $$ [$Hpkg $Hc $Hd $Hcch]
      inext; iintro -
      iapply HΦ $$ Hc
      imodintro; iintro #Hp; iexact Hp
  · iapply isCancelCtxOf_closedchan $$ Hc

end wps

end context

end Perennial
