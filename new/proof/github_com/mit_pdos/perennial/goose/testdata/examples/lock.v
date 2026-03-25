From New.proof Require Export proof_prelude.
From New.golang.theory Require Import chan.
From New.proof Require Import strings.
From New.golang.theory.chan.idioms Require Import
  base lock bag .
From New.proof Require Import time.
From New.generatedproof.github_com.mit_pdos.perennial.goose.testdata.examples.channel Require Import lock.
Import New.code.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.lock.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : lock.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) pkg_id.lock := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) pkg_id.lock := build_get_is_pkg_init_wf.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Definition is_Lock (γ : lock_channel_names) (l : lock.Lock.t) (R : iProp Σ) : iProp Σ :=
  "#Hlock_chan" ∷ is_lock_channel (V:=unit) γ (Lock.ch' l) R.

#[global] Instance is_Lock_persistent γ l R : Persistent (is_Lock γ l R) := _.


Lemma wp_NewLock (R : iProp Σ) :
  {{{ is_pkg_init pkg_id.lock ∗ ▷ R }}}
    @! lock.NewLock #()
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
  {{{ is_pkg_init pkg_id.lock ∗ is_Lock γ l R }}}
   l @! lock.Lock @! "Lock" #()
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
  {{{ is_pkg_init pkg_id.lock ∗
      is_Lock γ l R ∗ R }}}
   l @! lock.Lock @! "Unlock" #()
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
  {{{ is_pkg_init pkg_id.lock ∗ is_Lock γ l R }}}
   l @! lock.Lock @! "TryLock" #()
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

Lemma wp_Lock__LockWithTimeout γ (l : Lock.t) (R : iProp Σ) (d : time.Duration.t) :
  {{{ is_pkg_init pkg_id.lock ∗ is_Lock γ l R }}}
   l @! lock.Lock @! "LockWithTimeout" #d
  {{{ (b : bool), RET #b;
      if b then R else True }}}.
Proof.
  wp_start as "#HisLock".
  iNamed "HisLock".
  wp_auto.
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
