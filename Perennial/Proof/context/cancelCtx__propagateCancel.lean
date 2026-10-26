/-
The proof of `context.cancelCtx.propagateCancel` (`(*cancelCtx).propagateCancel`).
-/
module

public import Perennial.Spec.context.cancelCtx__propagateCancel
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.sync.atomic.Value__Load
public import Perennial.Spec.context.cancelCtx__Done
public import Perennial.Spec.context.cancelCtx__Err
public import Perennial.Spec.context.cancelCtx__Value
public import Perennial.Spec.context.cancelCtx__cancel
public import Perennial.Spec.context.Cause
public import Perennial.Proof.context.CancelCtxCells
public import Perennial.Proof.context.CancelCtxContext
public import Perennial.Proof.context.BackgroundCtx

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- The three cases, each proved as before (the local `have`s). -/
theorem context.cancelCtx.propagateCancel.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (wp_Cause : context.Cause.spec (GF := GF) (hG := hG)) :
    context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG) :=
  fun c parent k [SafeMapKey (GF := GF) context.canceler.ty k] => by
  have wp_err_Load_frag := wp_err_Load_frag_of wp_VLoad
  have wp_parentCancelCtx_self := wp_parentCancelCtx_self_of wp_cancelCtx_Done wp_cancelCtx_Value
      wp_VLoad
  have childCancelSpec_cancelCtx := childCancelSpec_cancelCtx_of wp_cancelCtx_cancel
  have wp_propagateCancel_background : ∀ (c : Loc) (k : GoInterface),
      {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
          ctxField c ↦ (interface.nil : GoInterface) }}
        (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
          (Val #(interface.ok backgroundCtxVal)))
          (Val #k))
      {{ RET #(); ctxField c ↦ (interface.ok backgroundCtxVal : GoInterface) }} :=
    fun c k => by
      wp_start as Hf
      wp_auto
      wp_apply wp_background_Done
      iapply HΦ $$ Hf

  have wp_propagateCancel_cancelCtx : ∀ (c : Loc) (γ : ContextNames) (P : IProp GF)
          (parent : GoInterfaceOk) (s : ContextDesc (IProp GF)),
      {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
          ctxField c ↦ (interface.nil : GoInterface) ∗
          (isContext parent s ∗ isCancelCtxCtx parent s ∗ □ (s.PDone -∗ P)) }}
        (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
          (Val #(interface.ok parent)))
          (Val #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c)))
      {{ RET #(); ctxField c ↦ (interface.ok parent : GoInterface) }} :=
    fun c γ P parent s => by
      wp_start as ⟨#Hc, Hf, #Hctx, #Hcc, #HPP⟩
      iunfold isCancelCtxCtx at Hcc
      icases Hcc with ⟨%p, %hp, #Hp⟩
      subst hp
      ihave #Hi := isCancelCtxOf_closedchan c γ P $$ Hc
      iunfold isClosedchanInit at Hi
      icases Hi with ⟨%cch, %γc, #Hcch, #Hcchan, #Hcinv⟩
      wp_auto
      wp_apply wp_cancelCtx_Done p _ _ $$ [$Hp] as %ch %γch ⟨#Hd, #Hfr⟩
      ihave #Hch := isContextDone_is_chan _ _ _ $$ Hd
      ihave %hnn := isChan_ne_nil _ _ $$ Hch
      rw [decide_eq_false hnn]
      wp_auto
      by_cases hcc : ch = cch
      · subst hcc
        iunfold doneFresh at Hfr
        icases Hfr with (⟨%cch', #Hcch', %hne⟩ | ⟨#Hpd, #Hcl⟩)
        · icombine Hcch Hcch' gives %heq
          exact absurd heq hne
        wp_apply_core chan.wp_select_nonblocking_alt [iprop(False)]
            iprop(c_ptr ↦ c ∗ child_ptr ↦ (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c : GoInterface) ∗
              parent_ptr ↦ (interface.ok (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) : GoInterface) ∗
              ctxField c ↦ (interface.ok (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) : GoInterface))
            $$ [HΦ] [c child parent Hf] []
        · iapply BigSepL2.bigSepL2_singleton.2
          iintro ⟨c, child, parent, Hf⟩
          simp only [chan.nonblockingAltClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
          isplitr
          · ipureintro; rfl
          isplitr
          · iexact Hcchan
          iapply closed_chan_nonblocking_receive $$ Hcinv
          wp_auto
          wp_apply wp_cancelCtx_Err p s.Done_gn s.PDone true $$ [$Hp]
            as %e ⟨%hne, He⟩
          · simp only [↓reduceIte]; iexact Hcl
          have hne := hne rfl
          rw [ite_eq_right hne]
          icases He with ⟨%htyped, -, -⟩
          wp_apply wp_Cause (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) s $$ [$Hctx]
            as %cause -
          wp_apply wp_cancelCtx_cancel c γ P false e cause htyped $$ [$Hc] as -
          · isplitl []
            · imodintro; iapply HPP $$ Hpd
            · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
          iapply HΦ $$ Hf
        · iframe
        · iintro - Hnr
          icases BigSepL.bigSepL_singleton.1 $$ Hnr with Hfalse
          iexfalso; iexact Hfalse
      wp_apply_core chan.wp_select_nonblocking_alt [iprop(⌜ch ≠ cch⌝)]
          iprop(c_ptr ↦ c ∗ child_ptr ↦ (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c : GoInterface) ∗
            parent_ptr ↦ (interface.ok (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) : GoInterface) ∗
            ctxField c ↦ (interface.ok (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) : GoInterface) ∗
            (ctxField c ↦ (interface.ok (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) : GoInterface)
              -∗ Φ #()))
          $$ [] [c child parent Hf HΦ] []
      · iapply BigSepL2.bigSepL2_singleton.2
        iintro ⟨c, child, parent, Hf, HΦ⟩
        simp only [chan.nonblockingAltClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
        isplitr
        · ipureintro; rfl
        isplitr
        · iexact Hch
        iapply isContextDone_nonblocking_receive _ _ _ _ _ $$ Hd
        isplit
        · iintro ⟨#Hpd, #Hcl⟩
          wp_auto
          wp_apply wp_cancelCtx_Err p s.Done_gn s.PDone true $$ [$Hp]
            as %e ⟨%hne, He⟩
          · simp only [↓reduceIte]; iexact Hcl
          have hne := hne rfl
          rw [ite_eq_right hne]
          icases He with ⟨%htyped, -, -⟩
          wp_apply wp_Cause (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) s $$ [$Hctx]
            as %cause -
          wp_apply wp_cancelCtx_cancel c γ P false e cause htyped $$ [$Hc] as -
          · isplitl []
            · imodintro; iapply HPP $$ Hpd
            · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
          iapply HΦ $$ Hf
        · iframe; ipureintro; exact hcc
      · iframe
      · iintro ⟨c, child, parent, Hf, HΦ⟩ -
        wp_auto
        ihave #Hdg := isContextDone_doneGn _ _ _ $$ Hd
        wp_apply wp_parentCancelCtx_self p s.Done_gn s.PDone ch cch hcc $$ [$Hp $Hdg $Hcch]
        ihave #Hp' := Hp
        iunfold isCancelCtxOf at Hp'
        icases Hp' with ⟨%Rp, #Hmup, #Hinvp, -⟩
        wp_apply wp_Lock $$ [$Hmup] as ⟨Hlocked, Hlk⟩
        iunfold cancelCtxLockInv at Hlk
        icases Hlk with ⟨%children, %cause, %od, %closed, Hchildren, Hcause, Hcl, Hod, HR⟩
        cases closed
        · simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hcl with ⟨Hcg, Hchs⟩
          wp_apply wp_err_Load_frag p _ _ false $$ [$Hp Hcg] as %e ⟨Hcg, Hhe⟩
          · unfold closedFrag; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hcg
          icases Hhe with ⟨%he, -, -⟩
          have he := he (by simp)
          subst he
          wp_auto
          iunfold childrenInv at Hchs
          icases Hchs with (%hnil | ⟨%M, HM, #Hspecs⟩)
          · subst hnil
            rw [show decide (map.nil = map.nil) = true from decide_eq_true rfl]
            wp_pures
            wp_apply (wp_map_make1 (K := GoInterface) (V := Unit) context.canceler.ty
              (go.GoType.StructType [])) as %m HM
            wp_apply (wp_mapInsert context.canceler.ty m (∅ : GMap GoInterface Unit)
              (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) ()) $$ [$HM] as HM
            ihave #Hcs := childCancelSpec_cancelCtx c γ P s.PDone $$ [$Hpkg $Hc $HPP]
            wp_apply wp_Unlock $$ [$Hmup $Hlocked Hchildren Hcause Hcg HM Hod HR]
            · inext; unfold cancelCtxLockInv
              iexists m, cause, od, false
              simp only [Bool.false_eq_true, ↓reduceIte, named]
              iframe
              unfold closedFrag; simp only [Bool.false_eq_true, ↓reduceIte]
              iframe
              unfold childrenInv
              iright
              iexists _
              iframe HM
              imodintro
              iintro %k %u %hk
              rw [GMap.lookup_insert_eq_iff] at hk
              split at hk
              · rename_i heq; subst heq; iexact Hcs
              · simp at hk
            iapply HΦ $$ Hf
          · icases ownMap_not_nil_dup _ _ $$ HM with ⟨HM, %hnn'⟩
            rw [show decide (children = map.nil) = false from decide_eq_false hnn']
            wp_pures
            wp_auto
            wp_apply (wp_mapInsert context.canceler.ty children M
              (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) ()) $$ [$HM] as HM
            ihave #Hcs := childCancelSpec_cancelCtx c γ P s.PDone $$ [$Hpkg $Hc $HPP]
            wp_apply wp_Unlock $$ [$Hmup $Hlocked Hchildren Hcause Hcg HM Hod HR]
            · inext; unfold cancelCtxLockInv
              iexists children, cause, od, false
              simp only [Bool.false_eq_true, ↓reduceIte, named]
              iframe
              unfold closedFrag; simp only [Bool.false_eq_true, ↓reduceIte]
              iframe
              unfold childrenInv
              iright
              iexists _
              iframe HM
              imodintro
              iintro %k %u %hk
              rw [GMap.lookup_insert_eq_iff] at hk
              split at hk
              · rename_i heq; subst heq; iexact Hcs
              · iapply Hspecs $$ %k %u %hk
            iapply HΦ $$ Hf
        · simp only [↓reduceIte]
          icases Hcl with ⟨#Hclosed, %hch⟩
          wp_apply wp_err_Load_frag p _ _ true $$ [$Hp] as %e ⟨-, Hhe⟩
          · unfold closedFrag; simp only [↓reduceIte]; iexact Hclosed
          icases Hhe with ⟨-, %ht, #Hpd⟩
          have ht := ht (by simp)
          cases e with
          | nil => exact absurd ht id
          | ok ie =>
          wp_auto
          erw [ite_eq_left ht]
          wp_auto
          wp_apply wp_cancelCtx_cancel c γ P false (GoInterface.ok ie) cause ht $$ [$Hc] as -
          · isplitl []
            · imodintro; iapply HPP; iapply Hpd; ipureintro; simp
            · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
          wp_apply wp_Unlock $$ [$Hmup $Hlocked Hchildren Hcause Hod HR]
          · inext; unfold cancelCtxLockInv
            iexists children, cause, od, true; simp only [↓reduceIte, named]; iframe; iframe #
            ipureintro; exact hch
          iapply HΦ $$ Hf

  have wp_propagateCancel_any : ∀ (c : Loc) (parent : GoInterfaceOk) (s : ContextDesc (IProp GF))
          (k : GoInterface) [SafeMapKey (GF := GF) context.canceler.ty k],
      {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
          ctxField c ↦ (interface.nil : GoInterface) ∗ isContext parent s ∗
          childCancelSpec iprop(True) k }}
        (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
          (Val #(interface.ok parent)))
          (Val #k))
      {{ RET #(); ctxField c ↦ (interface.ok parent : GoInterface) }} :=
    fun c parent s k [SafeMapKey (GF := GF) context.canceler.ty k] => by
      wp_start as ⟨Hf, #Hctx, #Hk⟩
      ihave #Hctx2 := Hctx
      iunfold isContext at Hctx2
      iunfold isContextDef at Hctx2
      icases Hctx2 with ⟨#HDeadline, #HDone, #HErr, #HValue, #HErrDone, #HDoneFresh, ⟨%hstop, #HPar⟩,
        #Hcci⟩
      ihave #Hi := Hcci
      iunfold isClosedchanInit at Hi
      icases Hi with ⟨%cch, %γc, #Hcch, #Hcchan, #Hcinv⟩
      cases k with
      | nil => simp only [childCancelSpec]; iexfalso; iexact Hk
      | ok ki =>
      wp_auto
      wp_apply HDone as %ch %γch #Hd
      ihave #Hch := isContextDone_is_chan _ _ _ $$ Hd
      ihave %hnn := isChan_ne_nil _ _ $$ Hch
      rw [decide_eq_false hnn]
      wp_auto
      ihave #Hdg := isContextDone_doneGn _ _ _ $$ Hd
      simp only [childCancelSpec]
      by_cases hcc : ch = cch
      · subst hcc
        imod HDoneFresh $$ Hdg with #Hfr
        iunfold doneFreshT at Hfr
        icases Hfr with (⟨%cch', #Hcch', %hne⟩ | #Hcl)
        · icombine Hcch Hcch' gives %heq
          exact absurd heq hne
        wp_apply_core chan.wp_select_nonblocking_alt [iprop(False)]
            iprop(c_ptr ↦ c ∗ child_ptr ↦ (GoInterface.ok ki) ∗
              parent_ptr ↦ (interface.ok parent : GoInterface) ∗
              ctxField c ↦ (interface.ok parent : GoInterface))
            $$ [HΦ] [c child parent Hf] []
        · iapply BigSepL2.bigSepL2_singleton.2
          iintro ⟨c, child, parent, Hf⟩
          simp only [chan.nonblockingAltClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
          isplitr
          · ipureintro; rfl
          isplitr
          · iexact Hcchan
          iapply closed_chan_nonblocking_receive $$ Hcinv
          wp_auto
          wp_apply HErrDone $$ Hcl as %e %htyped
          wp_apply wp_Cause parent s $$ [$Hctx] as %cause -
          wp_apply Hk
          · ipureintro; exact htyped
          · imodintro; itrivial
          iapply HΦ $$ Hf
        · iframe
        · iintro - Hnr
          icases BigSepL.bigSepL_singleton.1 $$ Hnr with Hfalse
          iexfalso; iexact Hfalse
      wp_apply_core chan.wp_select_nonblocking_alt [iprop(⌜ch ≠ cch⌝)]
          iprop(c_ptr ↦ c ∗ child_ptr ↦ (GoInterface.ok ki) ∗
            parent_ptr ↦ (interface.ok parent : GoInterface) ∗
            ctxField c ↦ (interface.ok parent : GoInterface) ∗
            (ctxField c ↦ (interface.ok parent : GoInterface) -∗ Φ #()))
          $$ [] [c child parent Hf HΦ] []
      · iapply BigSepL2.bigSepL2_singleton.2
        iintro ⟨c, child, parent, Hf, HΦ⟩
        simp only [chan.nonblockingAltClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
        isplitr
        · ipureintro; rfl
        isplitr
        · iexact Hch
        iapply isContextDone_nonblocking_receive _ _ _ _ _ $$ Hd
        isplit
        · iintro ⟨-, #Hcl⟩
          wp_auto
          wp_apply HErrDone $$ Hcl as %e %htyped
          wp_apply wp_Cause parent s $$ [$Hctx] as %cause -
          wp_apply Hk
          · ipureintro; exact htyped
          · imodintro; itrivial
          iapply HΦ $$ Hf
        · iframe; ipureintro; exact hcc
      · iframe
      · iintro ⟨c, child, parent, Hf, HΦ⟩ -
        wp_auto
        wp_bind (App (Val (@! context.parentCancelCtx)) _)
        iapply HPar $$ %ch %cch Hdg Hcch %hcc
        inext
        iintro %p #Hp
        iunfold isCancelCtx at Hp
        icases Hp with ⟨%γp, %Pp, #Hp⟩
        ihave #Hksp : childCancelSpec Pp (GoInterface.ok ki) $$ []
        · iapply childCancelSpec_true
          simp only [childCancelSpec]
          iexact Hk
        ihave #Hp' := Hp
        iunfold isCancelCtxOf at Hp'
        icases Hp' with ⟨%Rp, #Hmup, #Hinvp, -⟩
        wp_auto
        wp_apply wp_Lock $$ [$Hmup] as ⟨Hlocked, Hlk⟩
        iunfold cancelCtxLockInv at Hlk
        icases Hlk with ⟨%children, %cause, %od, %closed, Hchildren, Hcause, Hcl, Hod, HR⟩
        cases closed
        · simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hcl with ⟨Hcg, Hchs⟩
          wp_apply wp_err_Load_frag p _ _ false $$ [$Hp Hcg] as %e ⟨Hcg, Hhe⟩
          · unfold closedFrag; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hcg
          icases Hhe with ⟨%he, -, -⟩
          have he := he (by simp)
          subst he
          wp_auto
          iunfold childrenInv at Hchs
          icases Hchs with (%hnil | ⟨%M, HM, #Hspecs⟩)
          · subst hnil
            rw [show decide (map.nil = map.nil) = true from decide_eq_true rfl]
            wp_pures
            wp_apply (wp_map_make1 (K := GoInterface) (V := Unit) context.canceler.ty
              (go.GoType.StructType [])) as %m HM
            wp_apply (wp_mapInsert context.canceler.ty m (∅ : GMap GoInterface Unit)
              (GoInterface.ok ki) ()) $$ [$HM] as HM
            wp_apply wp_Unlock $$ [$Hmup $Hlocked Hchildren Hcause Hcg HM Hod HR]
            · inext; unfold cancelCtxLockInv
              iexists m, cause, od, false
              simp only [Bool.false_eq_true, ↓reduceIte, named]
              iframe
              unfold closedFrag; simp only [Bool.false_eq_true, ↓reduceIte]
              iframe
              unfold childrenInv
              iright
              iexists _
              iframe HM
              imodintro
              iintro %k %u %hk
              rw [GMap.lookup_insert_eq_iff] at hk
              split at hk
              · rename_i heq; subst heq; iexact Hksp
              · simp at hk
            iapply HΦ $$ Hf
          · icases ownMap_not_nil_dup _ _ $$ HM with ⟨HM, %hnn'⟩
            rw [show decide (children = map.nil) = false from decide_eq_false hnn']
            wp_pures
            wp_auto
            wp_apply (wp_mapInsert context.canceler.ty children M
              (GoInterface.ok ki) ()) $$ [$HM] as HM
            wp_apply wp_Unlock $$ [$Hmup $Hlocked Hchildren Hcause Hcg HM Hod HR]
            · inext; unfold cancelCtxLockInv
              iexists children, cause, od, false
              simp only [Bool.false_eq_true, ↓reduceIte, named]
              iframe
              unfold closedFrag; simp only [Bool.false_eq_true, ↓reduceIte]
              iframe
              unfold childrenInv
              iright
              iexists _
              iframe HM
              imodintro
              iintro %k %u %hk
              rw [GMap.lookup_insert_eq_iff] at hk
              split at hk
              · rename_i heq; subst heq; iexact Hksp
              · iapply Hspecs $$ %k %u %hk
            iapply HΦ $$ Hf
        · simp only [↓reduceIte]
          icases Hcl with ⟨#Hclosed, %hch⟩
          wp_apply wp_err_Load_frag p _ _ true $$ [$Hp] as %e ⟨-, Hhe⟩
          · unfold closedFrag; simp only [↓reduceIte]; iexact Hclosed
          icases Hhe with ⟨-, %ht, -⟩
          have ht := ht (by simp)
          cases e with
          | nil => exact absurd ht id
          | ok ie =>
          wp_auto
          erw [ite_eq_left ht]
          wp_auto
          wp_apply Hk
          · ipureintro; exact ht
          · imodintro; itrivial
          wp_apply wp_Unlock $$ [$Hmup $Hlocked Hchildren Hcause Hod HR]
          · inext; unfold cancelCtxLockInv
            iexists children, cause, od, true; simp only [↓reduceIte, named]; iframe; iframe #
            ipureintro; exact hch
          iapply HΦ $$ Hf
  iintro %Φ ⟨#Hpkg, Hf, Hcase⟩ HΦ
  icases Hcase with (%h | ⟨%γ, %P, %s, %hk, #Hc, #Hctx, #Hcc, #HPP⟩ | ⟨%s, #Hctx, #Hk⟩)
  · subst h
    iapply wp_propagateCancel_background c k $$ [$Hpkg $Hf] HΦ
  · subst hk
    iapply wp_propagateCancel_cancelCtx c γ P parent s $$ [$Hpkg $Hc $Hf $Hctx $Hcc $HPP] HΦ
  · iapply wp_propagateCancel_any c parent s k $$ [$Hpkg $Hf $Hctx $Hk] HΦ

end proof

end Perennial
