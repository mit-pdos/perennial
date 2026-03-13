From New.proof Require Export proof_prelude.
From New.golang.theory Require Import chan.
From New.proof Require Import strings.
From New.proof.github_com.goose_lang.goose.model.channel Require Import
  idiom.base lock bag.
From New.proof.github_com.goose_lang.goose.model.channel.idiom Require Import done.
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

Definition is_Lock (γ : lock_channel_names) (l : loc) (R : iProp Σ) : iProp Σ :=
  ∃ ch : loc,
    "ch" ∷ l.[chan_spec_raw_examples.Lock.t, "ch"] ↦□ ch ∗
    "#Hlock_chan" ∷ is_lock_channel (V:=unit) γ ch R.

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
  wp_apply wp_alloc.
  iIntros (l) "Hl".
  iStructNamed "Hl". 
  iPersist "ch".
  wp_auto.
  iMod (start_lock_channel (V:=unit) (t:=(go.StructType [])) ch R γch with "[$Hchan] [$Hoc] [HR]") as (γlock) "#Hislock".
  { done. }
  { iNext. iFrame. }
  iApply "HΦ".
  iExists ch. iFrame "#".
iModIntro. iFrame "#". 
Qed.

Lemma wp_Lock__Lock γ (l : loc) (R : iProp Σ) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_Lock γ l R }}}
   l @! (go.PointerType chan_spec_raw_examples.Lock) @! "Lock" #()
  {{{ RET #(); R }}}.
Proof.
  wp_start.
  iNamed "Hpre". 
  wp_auto.
  iDestruct (is_lock_channel_is_chan (t:=(go.StructType [])) with "Hlock_chan") as "#Hchan".
  
  wp_apply ((wp_lock_channel_lock (t:=(go.StructType [])) γ ch ) with "Hlock_chan").
  iIntros "Hlc".
  wp_auto.
  iApply "HΦ". iFrame.
Qed.

Lemma wp_Lock__Unlock γ (l : loc) (R : iProp Σ) :
  {{{ is_pkg_init chan_spec_raw_examples ∗
      is_Lock γ l R ∗ R }}}
   l @! (go.PointerType chan_spec_raw_examples.Lock) @! "Unlock" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start.
  iNamed "Hpre". 
  iDestruct "Hpre" as "(#Hheld & HR)".
  wp_auto.
  iNamed "Hheld".
  iDestruct (is_lock_channel_is_chan (t:=(go.StructType [])) with "Hlock_chan") as "#Hchan".
  wp_auto.
  wp_apply ((wp_lock_channel_unlock (t:=(go.StructType [])) γ ch ) with "[$Hlock_chan $HR ]").
  iIntros (v) "H". wp_auto. iApply "HΦ". done.
Qed.

Lemma wp_Lock__TryLock γ (l : loc) (R : iProp Σ) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_Lock γ l R }}}
   l @! (go.PointerType chan_spec_raw_examples.Lock) @! "TryLock" #()
  {{{ (b : bool), RET #b; if b then R else True }}}.
Proof.
  wp_start.
  iNamed "Hpre".
  wp_auto_lc 3.
   iRename select (£1) into "Hlc1".
   iCombine "ch" "Hlc1" as "H".
   iRename select (£1) into "Hlc2".
   iDestruct "H" as "[ch Hlc1]".
  iDestruct (is_lock_channel_is_chan (t:=go.StructType []) with "Hlock_chan") as "#Hchan".
  wp_apply (chan.wp_select_nonblocking).
  iSplit.
  - iDestruct "ch" as "#ch".
    simpl. iFrame "#". iExists _, _ .
    iSplitR; first done.
    iApply ((lock_channel_trylock_au(t:=go.StructType [])) with "[$Hlock_chan][Hlc1]").
    {
      done.
    }
    iIntros "Hl". wp_auto.
    iApply "HΦ". iFrame.
  - wp_auto.
    iApply "HΦ". done.
Qed.

Lemma wp_Lock__LockIfNotCancelled
    γlock (l done_ch : loc) (R Q : iProp Σ)
    (γdone : done_names) `{!Persistent Q}:
  {{{ is_pkg_init chan_spec_raw_examples ∗
      is_Lock γlock l R ∗
      is_done (V:=unit) γdone done_ch ∗
      BroadcastNotified γdone Q }}}
   l @! (go.PointerType chan_spec_raw_examples.Lock) @! "LockIfNotCancelled" #done_ch 
  {{{ (b : bool), RET #b;
      if b then R else Q }}}.
Proof.
  wp_start as "(#HisLock & #Hdone & #Hbnot)".
  iNamed "HisLock".
  wp_auto_lc 5. 
  iRename select (£1) into "Hlc".
  iDestruct (is_lock_channel_is_chan (t:=go.StructType []) with "Hlock_chan") as "#Hchan".
  iDestruct (done_is_chan (V:=unit) (t:=go.StructType []) γdone done_ch with "Hdone") as "#Hdone_chan".
  wp_apply chan.wp_select_blocking.
  iAssert (£ 4 ∗ £ 1)%I with "[-HΦ]" as "[Hlc4 Hlc1]".
  {
    iFrame. 
    replace 4%nat with (3 + 1)%nat by done.
    rewrite lc_split . iFrame.
    replace 3%nat with (2 + 1)%nat by done.
    rewrite lc_split . iFrame.
    replace 2%nat with (1 + 1)%nat by done.
    rewrite lc_split . iFrame.
  }
  simpl.
  iSplit.
  - simpl. iExists unit, ch, γlock.(lchan_name), tt, _, _, _.
    iSplitR; first done. iFrame "#".
    iApply (lock_channel_lock_au (t:=go.StructType [])  with "[$Hlock_chan][$Hlc1]").
    iNext. iIntros "HR".
    wp_auto. iApply "HΦ". iFrame.
  - iSplitL; last done.
    simpl. iExists unit, done_ch, γdone.(chan_name),  _, _,_.
    iFrame "#". iFrame.
    iSplitR; first done.
    iApply (done_receive_broadcast_au (V:=unit) (t:=go.StructType [])  with "[$Hdone] [$Hbnot] [HΦ] [Hlc4]").
    { iNext. iIntros "HQ". wp_auto. iApply "HΦ". done.  }
    {
    replace 4%nat with (3 + 1)%nat by done.
    rewrite lc_split . iFrame.
    replace 3%nat with (2 + 1)%nat by done.
    rewrite lc_split . iFrame.
    replace 2%nat with (1 + 1)%nat by done.
    rewrite lc_split . iFrame.
    iDestruct "Hlc4" as "(Hlc1 & Hlc2)".
    iFrame.
    iDestruct "Hlc1" as "(Hlc1 & Hlc2)".
    iFrame.
    }
Qed.

Lemma wp_Lock__LockWithTimeout γ (l : loc) (R : iProp Σ) (d : time.Duration.t) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_Lock γ l R }}}
   l @! (go.PointerType chan_spec_raw_examples.Lock) @! "LockWithTimeout" #d 
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
  - simpl. iExists unit, ch, γ.(lchan_name), tt, _, _, _.
    iSplitR; first done. iFrame "#".
    iSplitL "". {
    iApply (is_lock_channel_is_chan (V:=unit) (t:=(go.StructType []))).
    iFrame "#".
    }
    iFrame "#". 
    iApply (lock_channel_lock_au (t:=go.StructType [])  with "[$Hlock_chan][$]").
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

Lemma wp_Lock__LockWithDeadline γ (l : loc) (R : iProp Σ) (deadline : time.Time.t) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_Lock γ l R }}}
   l @! (go.PointerType chan_spec_raw_examples.Lock) @! "LockWithDeadline" #deadline 
  {{{ (b : bool), RET #b;
      if b then R else True }}}.
Proof.
  wp_start as "#HisLock".
  wp_auto.
  wp_apply wp_Until.
  iIntros (d) "_". wp_auto.
  wp_apply (wp_Lock__LockWithTimeout γ l R d with "[$HisLock] [HΦ]").
  iIntros (b) "Hb".
  wp_auto.
  iApply "HΦ". iFrame.
Qed.

End proof.
