/-
The proof of `context.(*cancelCtx).cancel`.
-/
module

public import Perennial.Spec.context.cancelCtx__cancel
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.sync.atomic.Value__Load
public import Perennial.Spec.sync.atomic.Value__Store
public import Perennial.Spec.context.removeChild
public import Perennial.Proof.context.CancelCtxCells

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

theorem context.cancelCtx.cancel.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (wp_VStore : sync.atomic.Value.Store.spec (GF := GF) (hG := hG))
    (wp_removeChild : context.removeChild.spec (GF := GF) (hG := hG)) :
    context.cancelCtx.cancel.spec (GF := GF) (hG := hG) := fun c γ P rm err cause herr => by
  have wp_done_Load_frag := wp_done_Load_frag_of wp_VLoad
  have wp_err_Load_frag := wp_err_Load_frag_of wp_VLoad
  wp_start as ⟨#Hc, #Hp, Hrm⟩
  ihave #Hc' := Hc
  iunfold isCancelCtxOf at Hc'
  iNamed Hc'
  ihave #Hi := Hcci
  iunfold isClosedchanInit at Hi
  icases Hi with ⟨%cch, %γc, #Hcch, #Hcchan, #Hcinv⟩
  cases err with
  | nil => exact absurd herr id
  | ok ierr =>
  wp_auto
  cases cause <;> wp_auto
  all_goals
    wp_apply wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
    unfold cancelCtxLockInv
    icases Hlk with ⟨%children, %cause0, %od, %closed, Hchildren, Hcause, Hcl, Hod, HR⟩
    cases closed
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hcl with ⟨Hcg, Hch⟩
      wp_apply wp_err_Load_frag c γ P false $$ [$Hc Hcg] as %e ⟨Hcg, Hhe⟩
      · unfold closedFrag; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hcg
      icases Hhe with ⟨%he, -, -⟩
      have he := he (by simp)
      subst he
      wp_auto
      unfold closedFrag
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_apply_core (wp_VStore _ (interface.ok ierr) (by simp)) $$ [] [-]
      · iPkgInit
      iinv Hinv with Hi Hclose
      all_goals try solve_ndisj
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      unfold cancelCtxInv
      icases Hi with ⟨%od', %e, Hdone, Hdg, Herr, Hcg'⟩
      by_cases he : e = interface.nil
      · subst he
        simp only [ite_true]
        iframe Herr
        iintro Herr
        imod dghostVar_update_halves true _ _ _ $$ Hcg Hcg' with ⟨Hcg, Hcg'⟩
        imod dghostVar_persist _ _ _ $$ Hcg with #Hclosed
        imod Hmask with -
        imod Hclose $$ [Hdone Hdg Herr] with -
        · inext; iexists od', interface.ok ierr; iframe
          simp only [named]
          rw [ite_eq_right (by simp)]
          unfold ContextClosed
          iframe #
          ipureintro; exact herr
        imodintro
        wp_auto
        iclear Hcg'
        cases od
        case' none =>
          icases Hod with ⟨Hdgf, -⟩
          wp_apply wp_done_Load_frag c γ P none $$ [$Hc Hdgf] as ⟨Hdgf, -⟩
          · unfold doneFrag; iexact Hdgf
          unfold doneFrag; dsimp only [doneAny]
          wp_apply_core (wp_VStore _
              (interface.mkOk (go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType [])) #cch)
              (by simp)) $$ [] [-]
          · iPkgInit
          iinv Hinv with Hi Hclose
          all_goals try solve_ndisj
          iapply fupd_mask_intro Std.LawfulSet.empty_subset
          iintro Hmask
          inext
          icases Hi with ⟨%od', %e', Hdone, Hdg, Herr, Hcg'⟩
          cases od'
          case some ch' =>
            icases Hdg with ⟨%γ', Hd', -⟩
            rw [isContextDone_unseal]; unfold isContextDoneDef cdesc
            icases Hd' with ⟨Hd', -⟩
            ihave %h := dghostVar_agree _ _ _ _ _ $$ Hd' Hdgf
            cases h
          dsimp only [doneAny]
          iframe Hdone
          iintro Hdone
          imod dghostVar_update_halves (some cch) _ _ _ $$ Hdgf Hdg with ⟨Hdgf, Hdg⟩
          imod dghostVar_persist _ _ _ $$ Hdgf with #Hdgf
          imod Hmask with -
          imod Hclose $$ [Hdone Herr Hcg'] with -
          · inext; iexists (some cch), e'; iframe
            iexists γc
            isplitl []
            · rw [isContextDone_unseal]; unfold isContextDoneDef cdesc
              isplitl []
              · iexact Hdgf
              iright
              unfold ContextClosed
              iframe #
            · unfold doneFresh; iright; unfold ContextClosed; iframe #
          imodintro
          wp_auto
        case' some ch =>
          icases Hod with ⟨#Hdgf, %γch, Hpend⟩
          wp_apply wp_done_Load_frag c γ P (some ch) $$ [$Hc] as ⟨-, -⟩
          · unfold doneFrag; iexact Hdgf
          dsimp only [doneAny]
          ihave #Hchp := ownBroadcastChan_is_chan _ _ _ _ $$ Hpend
          ihave %hnn := isChan_ne_nil _ _ $$ Hchp
          rw [decide_eq_false hnn]
          wp_auto
          wp_apply wp_broadcast_chan_close ch γch iprop(P ∗ ContextClosed γ) $$ [$Hpend] as -
          · imodintro; unfold ContextClosed; iframe #
        all_goals
          iunfold childrenInv at Hch
          wp_func_lits
          icases Hch with (%hnil | ⟨%M, HM, #Hspecs⟩)
          all_goals first
            | (subst hnil
               wp_auto)
            | (wp_bind (App (App (Val (map.forRange _ _)) _) _)
               iapply (wp_map_for_range (fun _ _ => iprop(∃ (v cv : GoInterface),
                  child_ptr ↦ v ∗ err_ptr ↦ GoInterface.ok ierr ∗ cause_ptr ↦ cv))) $$ HM
               iintro %keys %hkeys
               isplitl [child err cause]
               · iexists _, _; iframe
               isplitl []
               · imodintro
                 iintro %i %key %u ⟨%hk1, %hk2⟩ ⟨%v, %cv, Hchild, Herr, Hcause⟩
                 ihave #Hsp := Hspecs $$ %key %u %hk2
                 cases key with
                 | nil => simp only [childCancelSpec]; iexfalso; iexact Hsp
                 | ok ki =>
                 simp only [childCancelSpec]
                 wp_auto
                 wp_apply Hsp
                 · ipureintro; exact herr
                 · iexact Hp
                 unfold forMapPostcondition
                 iright; ileft
                 isplit
                 · ipureintro; rfl
                 · iexists _, _; iframe
               iintro ⟨%v, %cv, child, err, cause⟩ HM
               wp_auto)
          all_goals
            wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause HR]
            · inext
              ihave H := cancelCtxLockInv_closed c γ P R _ _ $$ [] Hdgf Hchildren Hcause HR
              · unfold ContextClosed; iexact Hclosed
              iunfold cancelCtxLockInv at H
              iexact H
            cases rm
            · wp_auto
              iapply HΦ; unfold ContextClosed; iexact Hclosed
            · simp only [↓reduceIte]
              icases Hrm with ⟨%parent, #Hpf, #Hpar⟩
              wp_auto
              wp_apply wp_removeChild parent (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) $$ [$Hpar]
              iapply HΦ; unfold ContextClosed; iexact Hclosed
      · rw [ite_eq_right he]
        icases Hcg' with ⟨-, -, Hc2⟩
        unfold ContextClosed
        ihave %h := dghostVar_agree _ _ _ _ _ $$ Hcg Hc2
        cases h
    · simp only [↓reduceIte]
      icases Hcl with ⟨#Hclosed, %hch⟩
      wp_apply wp_err_Load_frag c γ P true $$ [$Hc] as %e ⟨-, Hhe⟩
      · unfold closedFrag; simp only [↓reduceIte]; iexact Hclosed
      icases Hhe with ⟨-, %ht, -⟩
      have ht := ht (by simp)
      cases e with
      | nil => exact absurd ht id
      | ok ie =>
      wp_auto
      wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hod HR]
      · inext; iexists children, _, od, true; simp only [↓reduceIte, named]; iframe; iframe #
        ipureintro; exact hch
      iapply HΦ $$ Hclosed

end proof

end Perennial
