/-
A `*cancelCtx` is a context: `isContext_cancelCtx_of` (from the specs of its methods), its
`childCancelSpec` (`childCancelSpec_cancelCtx_of`), and `parentCancelCtx(c)` for a `*cancelCtx`
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
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
  wp_alloc par as Hpar
  wp_pures
  wp_load
  wp_pures
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

/-- The `childCancelSpec` of a `*cancelCtx` child whose Done proposition follows from the
parent's. -/
theorem childCancelSpec_cancelCtx_of
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P Q : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗ □ (Q -∗ P) ⊢
      childCancelSpec Q (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) := by
  iintro ⟨#Hpkg, #Hc, #HQ⟩
  simp only [childCancelSpec]
  imodintro
  iintro %err %cause %Φ %herr #Hq HΦ
  iapply wp_cancelCtx_cancel c γ P false err cause herr $$ [$Hpkg $Hc]
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
      iintro %e ⟨%hne, -⟩
      iapply HΦ
      ipureintro; exact hne rfl
    all_goals
      iapply wp_cancelCtx_Err c _ _ false $$ [$Hpkg $Hc]
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      inext
      iintro %e ⟨-, He⟩
      iapply HΦ
      dsimp only
      by_cases he : e = interface.nil
      · subst he; simp only [ite_true]; itrivial
      · rw [ite_eq_right he]; rw [ite_eq_right he] at *
        icases He with ⟨-, #Hp, #Hcl⟩
        iframe #
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
    icases He with ⟨%ht, -⟩
    iapply HΦ; ipureintro; exact ht
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
      iapply HΦ
      unfold isCancelCtx; iexists _, _; iexact Hc
  · iapply isCancelCtxOf_closedchan $$ Hc

end wps

end context

end Perennial
