/-
The proof of `etcd_session.monitorSession`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.monitorSession
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.waitForSessionExpiration
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.newSession

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

set_option goose.wp.extras true

set_option maxHeartbeats 1600000 in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.monitorSession.wp_proof
    (wp_waitForSessionExpiration :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.waitForSessionExpiration.spec
        (GF := GF) (hG := hG))
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_newSession :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.newSession.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.monitorSession.spec
      (GF := GF) (hG := hG) := fun ch γch => by
  wp_start as ⟨sessionc, Hsessionc, #Hsessionc_is⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg $$ []
  · iPkgInit
  ihave #Hmu := isInv_access $$ Hpkg
  ihave HH : (∃ (ch : GoChan) (γch : ChanNames) (cst : Broadcast),
      "sessionc" ∷ typedPointsto (globalAddr sessionc) ch (DFrac.own (1 : Qp).half) ∗
      "Hsessionc" ∷ ownBroadcastChan ch γch iprop(True) cst ∗
      "#Hsessionc_is" ∷ isChan ch γch Unit ∗
      "%Hcst" ∷ ⌜cst ≠ Broadcast.Unknown⌝ : IProp GF) $$ [sessionc Hsessionc]
  · iexists ch, γch, Broadcast.Pending
    iframe
    iframe #
    ipureintro; simp
  iclear Hsessionc_is
  wp_for HH
  wp_apply wp_waitForSessionExpiration
  wp_apply wp_Mutex_Lock $$ [$Hmu] as ⟨Hlocked, Hown⟩
  icases Hown with ⟨%ch', %γch', sessionc_inv, #Hsessionc_inv, #Hsessionc_is_inv⟩
  icombine sessionc sessionc_inv gives %Heq
  subst Heq
  ihave sessionc := (pointsto_halves _ _).2 $$ [sessionc sessionc_inv]
  · iframe
  wp_bind (App (Val (GoInstruction SelectStmt)) _)
  iapply wp_wand (Φ := monitorSelectPost) $$ [sessionc Hsessionc] [-]
  · iapply chan.wp_select_nonblocking_alt [iprop(⌜cst = Broadcast.Pending⌝)]
      iprop(typedPointsto (globalAddr sessionc) ch (DFrac.own 1) ∗
        ownBroadcastChan ch γch iprop(True) cst) $$ [] [sessionc Hsessionc] []
    · iapply BigSepL2.bigSepL2_cons.2
      isplitl
      · iintro ⟨sessionc, Hsessionc⟩
        simp only [chan.nonblockingAltClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
        isplit
        · ipureintro; rfl
        isplit
        · iexact Hsessionc_is
        iapply ownBroadcastChan_nonblocking_receive _ _ _ _ _ cst $$ Hsessionc
        cases cst
        · dsimp only
          isplit
          · itrivial
          · iintro Hsessionc
            iframe
            ipureintro; rfl
        · dsimp only
          isplit
          · iintro #Hdone
            wp_auto
            iapply wp_fupd
            wp_apply chan.wp_make1 (V := Unit) as %ch2 %γ2 ⟨#Hch2, %_, Hoc⟩
            imod alloc_broadcast_chan (E := ⊤) iprop(True) γ2 ch2 $$ Hch2 Hoc with Hbc
            imodintro
            isplit
            · ipureintro; rfl
            iexists ch2, γ2
            iframe
            iframe #
          · itrivial
        · exact absurd rfl Hcst
      · iapply BigSepL2.bigSepL2_nil.2
        iempintro
    · iframe
    · iintro ⟨sessionc, Hsessionc⟩ Hnrs
      icases BigSepL.bigSepL_cons.1 $$ Hnrs with ⟨%Hp, -⟩
      subst Hp
      wp_auto
      isplit
      · ipureintro; rfl
      iexists ch, γch
      iframe
      iframe #
  iintro %v ⟨%Hv, %ch2, %γ2, sessionc, Hsessionc, #Hsessionc_is2⟩
  subst Hv
  wp_auto
  icases (pointsto_halves _ _).1 $$ sessionc with ⟨sessionc, sessionc_inv⟩
  -- Subtlety here: because we are deriving a persistent
  -- ownBroadcastChan(ch, broadcast.Pending), the function can retain Hsessionc
  -- asserting that the channel is specifically Pending; this is needed after the
  -- Unlock to safely close.
  ihave #Hunk := ownBroadcastChan_Unknown _ _ _ _ $$ Hsessionc
  wp_apply wp_Mutex_Unlock $$ [$Hmu $Hlocked sessionc_inv]
  · inext; iexists ch2, γ2; iframe; iframe #
  wp_apply wp_newSession as %err _
  cases err with
  | nil =>
    wp_auto
    wp_apply wp_Mutex_Lock $$ [$Hmu] as ⟨Hlocked, Hown⟩
    icases Hown with ⟨%ch3, %γ3, sessionc_inv, #Hsessionc_inv3, #Hsessionc_is_inv3⟩
    icombine sessionc sessionc_inv gives %Heq
    subst Heq
    wp_apply wp_broadcast_chan_close ch2 γ2 iprop(True) $$ [$Hsessionc] as #Hdone
    · imodintro; itrivial
    wp_apply wp_Mutex_Unlock $$ [$Hmu $Hlocked sessionc_inv]
    · inext; iexists ch2, γ3; iframe; iframe #
    wp_for_post
    iframe
    iexists ch2, γ2, Broadcast.Done
    iframe
    iframe #
    ipureintro; simp
  | ok e =>
    wp_auto
    wp_for_post
    iframe
    iexists ch2, γ2, Broadcast.Pending
    iframe
    iframe #
    ipureintro; simp

end proof

end Perennial
