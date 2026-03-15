From New.proof Require Export proof_prelude.
From New.golang.theory Require Import chan.
From New.proof Require Import strings.
From New.proof.github_com.goose_lang.goose.model.channel Require Import
  idiom.base lock bag.
From New.proof Require Import github_com.goose_lang.goose.model.channel.idiom.closeable.closeable.
From New.proof Require Import time.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.
Import New.code.github_com.goose_lang.goose.testdata.examples.channel.chan_spec_raw_examples.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : chan_spec_raw_examples.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) chan_spec_raw_examples := build_get_is_pkg_init_wf.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Definition is_Lock (γ : lock_channel_names) (l : chan_spec_raw_examples.Lock.t) (R : iProp Σ) : iProp Σ :=
  "#Hlock_chan" ∷ is_lock_channel (V:=unit) γ (Lock.ch' l) R.

#[global] Instance is_Lock_persistent γ l R : Persistent (is_Lock γ l R) := _.


Lemma wp_NewLock (R : iProp Σ) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ ▷ R }}}
    @! chan_spec_raw_examples.NewLock #()
  {{{ γ l, RET #l; is_Lock γ l R }}}.
  Proof using ext ffi ffi_interp0 ffi_semantics0 hG package_sem sem Σ.
  wp_start as "HR". 
  wp_apply chan.wp_make2; first done.
  iIntros (ch γch) "(#Hchan & %Hcap & Hoc)".
  rewrite -wp_fupd.
  wp_auto.
  iMod (start_lock_channel (V:=unit) (t:=(go.StructType [])) ch R γch with "[$Hchan] [$Hoc] [HR]") as (γlock) "#Hislock".
  { done. }
  { iNext. iFrame. }
  iModIntro.
  iApply "HΦ".
  rewrite /is_Lock. iFrame "#".
Qed.

Lemma wp_Lock__Lock γ l (R : iProp Σ) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_Lock γ l R }}}
   l @! chan_spec_raw_examples.Lock @! "Lock" #()
  {{{ RET #(); R }}}.
Proof.
  wp_start.
  iNamed "Hpre". 
  wp_auto.
  wp_apply ((wp_lock_channel_lock (t:=(go.StructType [])) γ l.(Lock.ch') ) with "[$Hchan //]").
  iIntros "HR".
  wp_auto.
  iApply "HΦ". iFrame.
Qed.

Lemma wp_Lock__Unlock γ l (R : iProp Σ) :
  {{{ is_pkg_init chan_spec_raw_examples ∗
      is_Lock γ l R ∗ R }}}
   l @! chan_spec_raw_examples.Lock @! "Unlock" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start.
  iNamed "Hpre". 
  iDestruct "Hpre" as "(#Hheld & HR)".
  wp_auto.
  iNamed "Hheld".
  wp_apply ((wp_lock_channel_unlock (t:=(go.StructType [])) γ l.(Lock.ch') ) with "[$Hchan HR]").
  { iFrame "#". iFrame. }
  iIntros (v) "H". wp_auto. iApply "HΦ". done.
Qed.

Lemma wp_Lock__TryLock γ (l : Lock.t) (R : iProp Σ) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_Lock γ l R }}}
   l @! chan_spec_raw_examples.Lock @! "TryLock" #()
  {{{ (b : bool), RET #b; if b then R else True }}}.
Proof.
  wp_start.
  iNamed "Hpre".
  wp_auto_lc 1.
  wp_apply (chan.wp_select_nonblocking).
  iSplit.
  - simpl. iFrame "#". iExists _, _ .
    iSplitR; first done.
    iApply ((lock_channel_nonblocking_send_au(t:=go.StructType [])) with "[$Hchan $Hinv] [$]").
    iIntros "Hl". wp_auto.
    iApply "HΦ". iFrame.
  - wp_auto.
    iApply "HΦ". done.
Qed.

Lemma wp_Lock__LockIfNotCancelled
    γlock (l: Lock.t) (done_ch : chan.t) (R Q : iProp Σ)
    (γdone : chan_names) `{!Persistent Q}:
  {{{ is_pkg_init chan_spec_raw_examples ∗
      is_Lock γlock l R ∗
      own_closeable_chan done_ch γdone Q closeable.Unknown }}}
   l @! chan_spec_raw_examples.Lock @! "LockIfNotCancelled" #done_ch
  {{{ (b : bool), RET #b;
      if b then R else Q }}}.
Proof.
  wp_start as "(#HisLock & #Hdone_closeable)".
  iNamed "HisLock".
  iDestruct (own_closeable_chan_is_chan with "Hdone_closeable") as "#Hdone_chan".
  wp_auto_lc 4.
  iRename select (£1) into "Hlc".
  wp_apply chan.wp_select_blocking.
  simpl.
  iSplit.
  - simpl. iExists unit, l.(Lock.ch'), γlock.(lchan_name), tt, _, _, _.
    iSplitR; first done. iFrame "#".
    iApply (lock_channel_send_au (t:=go.StructType [])  with "[$Hchan $Hinv][$]").
    iNext. iIntros "HR".
    wp_auto. iApply "HΦ". iFrame.
  - iSplitL; last done.
    simpl. iExists unit, done_ch, γdone, _, _,_.
    iFrame "#". iFrame.
    iSplitR; first done.
    iApply (closeable_chan_receive with "Hdone_closeable [HΦ]").
    { iIntros "[#HQ _]". wp_auto. iApply "HΦ". done. }
Qed.

Lemma wp_Lock__LockWithTimeout γ (l : Lock.t) (R : iProp Σ) (d : time.Duration.t) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_Lock γ l R }}}
   l @! chan_spec_raw_examples.Lock @! "LockWithTimeout" #d
  {{{ (b : bool), RET #b;
      if b then R else True }}}.
Proof.
  wp_start as "#HisLock".
  iNamed "HisLock".
  wp_auto.
  wp_if_destruct.
  { iApply "HΦ". done. }
  wp_bind.
  wp_apply (wp_After).
  iIntros (after_ch γafter_ch) "#Hafter_chan".
  wp_auto_lc 2. 
  wp_apply chan.wp_select_blocking. simpl.
   iSplit.
  - simpl. iExists unit, l.(Lock.ch'), γ.(lchan_name), tt, _, _, _.
    iSplitR; first done. iFrame "#".
    iApply (lock_channel_send_au (t:=go.StructType [])  with "[$Hchan $Hinv] [$]").
    iNext. iIntros "HR".
    wp_auto. iApply "HΦ". iFrame.
  - iSplitL; last done.
    simpl. iExists time.Time.t, after_ch.
    iFrame "#". iFrame. 
     repeat iExists _.
    iSplitR; first done. 
    iDestruct (is_bag_is_chan with "Hafter_chan") as "#H".
    iFrame "#".
    iApply (bag_recv_au with "[$] [$Hafter_chan]").
    iNext. iIntros (t). iIntros "Ht". wp_auto. iApply "HΦ". done.
Qed.

End proof.
