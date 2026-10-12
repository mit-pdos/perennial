/-
The proof of `context.(*cancelCtx).Done`.
-/
module

public import Perennial.Spec.context.cancelCtx__Done
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.sync.atomic.Value__Load
public import Perennial.Spec.sync.atomic.Value__Store
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

theorem context.cancelCtx.Done.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (wp_VStore : sync.atomic.Value.Store.spec (GF := GF) (hG := hG)) :
    context.cancelCtx.Done.spec (GF := GF) (hG := hG) := fun c γ P => by
  have wp_done_Load := wp_done_Load_of wp_VLoad
  have wp_done_Load_frag := wp_done_Load_frag_of wp_VLoad
  wp_start as #Hc
  ihave #Hc' := Hc
  iunfold isCancelCtxOf at Hc'
  iNamed Hc'
  iapply wp_with_defer
  iintro %defer Hdefer
  wp_auto
  wp_apply wp_done_Load $$ [$Hc] as %od Hod
  cases od with
  | some ch =>
    icases Hod with ⟨%γch, #Hd, #Hfr⟩
    dsimp only [doneAny]
    wp_auto
    iapply HΦ; iframe #
  | none =>
    dsimp only [doneAny]
    wp_auto
    wp_apply wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
    unfold cancelCtxLockInv
    icases Hlk with ⟨%children, %cause, %od, %closed, Hchildren, Hcause, Hcl, Hod, HR⟩
    cases od with
    | some ch =>
      icases Hod with ⟨#Hdg, Hpend⟩
      wp_apply wp_done_Load_frag c γ P (some ch) $$ [$Hc Hdg] as ⟨-, Hd⟩
      · unfold doneFrag; iexact Hdg
      icases Hd with ⟨%γch, #Hd, #Hfr⟩
      wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hpend HR]
      · inext; iexists children, cause, some ch, closed; dsimp only; simp only [named]
        iframe; iframe #
      iapply HΦ; iframe #
    | none =>
      icases Hod with ⟨Hdg, %hcl⟩
      wp_apply wp_done_Load_frag c γ P none $$ [$Hc Hdg] as ⟨Hdg, -⟩
      · unfold doneFrag; iexact Hdg
      unfold doneFrag
      dsimp only [doneAny]
      ihave #Hi := Hcci
      iunfold isClosedchanInit at Hi
      icases Hi with ⟨%cch, %γc, #Hcch, #Hcchan, -⟩
      ihave #Hcap := chan.isChan_cap _ _ $$ Hcchan
      wp_apply chan.wp_make1_ne (V := Unit) cch γc.chanCap $$ [$Hcap]
        as %ch %γch ⟨#Hch, %hcap, Hoc, %hfresh⟩
      imod alloc_broadcast_chan iprop(P ∗ ContextClosed γ) γch ch $$ Hch Hoc with Hbc
      ihave #Hbcu := ownBroadcastChan_Unknown _ _ _ _ $$ Hbc
      wp_apply_core (wp_VStore _
          (interface.mkOk (go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType [])) #ch)
          (by simp)) $$ [] [-]
      · iPkgInit
      iinv Hinv with Hi Hclose
      all_goals try solve_ndisj
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      unfold cancelCtxInv
      icases Hi with ⟨%od', %e, Hdone, Hdg', Herr, Hcg⟩
      cases od' with
      | some ch' =>
        icases Hdg' with ⟨%γ', Hd', -⟩
        rw [isContextDone_unseal]; unfold isContextDoneDef cdesc
        icases Hd' with ⟨Hd', -⟩
        ihave %h := dghostVar_agree _ _ _ _ _ $$ Hd' Hdg
        cases h
      | none =>
        dsimp only [doneAny]
        iframe Hdone
        iintro Hdone
        imod dghostVar_update_halves (some ch) _ _ _ $$ Hdg Hdg' with ⟨Hdg, Hdg'⟩
        imod dghostVar_persist _ _ _ $$ Hdg with #Hdg
        imod Hmask with -
        imod Hclose $$ [Hdone Herr Hcg] with -
        · inext; iexists (some ch), e; iframe
          iexists γch
          isplitl []
          · iapply isContextDone_of_broadcast $$ Hdg Hbcu
          · unfold doneFresh; ileft; iexists cch; iframe #; ipureintro; exact hfresh
        imodintro
        wp_auto
        subst hcl
        wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hbc HR]
        · inext; iexists children, cause, some ch, false; dsimp only; simp only [named]
          iframe; iframe #; simp only [Bool.false_eq_true, ↓reduceIte]; iexists γch; iframe
        iapply HΦ
        isplitl []
        · iapply isContextDone_of_broadcast $$ Hdg Hbcu
        · unfold doneFresh; ileft; iexists cch; iframe #; ipureintro; exact hfresh

end proof

end Perennial
