From New.proof.github_com.goose_lang.goose.testdata.examples Require Import channel_examples_init.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import idiom.base bag handshake closeable join.
From New.proof Require Import strings time sync.
From iris.base_logic Require Import ghost_map.
From New.golang Require Import theory.
From New.proof Require Import strings.
From New.code Require Import github_com.goose_lang.goose.testdata.examples.channel.
Import chan_spec_raw_examples.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : chan_spec_raw_examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Section hedged_example.
Context `{!chan_idiomG Σ go_string}.
Context `{!ghost_map.ghost_mapG Σ gname (go_string → iProp Σ)}.
Context `{!inG Σ unitR}.

Lemma wp_GetPrimary (q : go_string) :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.GetPrimary #q
  {{{ RET #(q ++ "_primary.html"%go); True }}}.
Proof. wp_start. wp_auto. iApply "HΦ". done. Qed.

Lemma wp_GetSecondary (q : go_string) :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.GetSecondary #q
  {{{ RET #(q ++ "_secondary.html"%go); True }}}.
Proof. wp_start. wp_auto. iApply "HΦ". done. Qed.

Lemma wp_CancellableHedgedRequest (query : go_string)
    (hedgeThreshold : time.Duration.t)
    (errStr_ptr' : loc)
    (done_ch : chan.t) (γdone : chan_names) :
  {{{ is_pkg_init chan_spec_raw_examples ∗
      own_closeable_chan done_ch γdone True closeable.Unknown ∗
      errStr_ptr' ↦ ""%go }}}
    @! chan_spec_raw_examples.CancellableHedgedRequest
         #query #hedgeThreshold #errStr_ptr' #done_ch
  {{{ (v : go_string) (b : bool),
      RET #(chan_spec_raw_examples.Result.mk v b);
      (* Primary won. *)
      ⌜(v = query ++ "_primary.html"%go ∧ b = true) ∨
      (* Hedged request won. *)
       (v = query ++ "_secondary.html"%go ∧ b = false)⌝ ∨
      (* Done channel closed before any result arrived — caller wrote
         "cancelled" into errStr_ptr' and we return the zero Result.  *)
      (errStr_ptr' ↦ "cancelled"%go ∗ ⌜v = ""%go ∧ b = false⌝) }}}.
Proof.
  wp_start as "(#Hdone_closeable & HerrStr)".
  iDestruct (own_closeable_chan_is_chan with "Hdone_closeable") as "#Hdone_chan".
  wp_auto.
  wp_apply chan.wp_make2; first done.
  iIntros (c γc) "(#Hc_is_chan & _ & Hc_own)".
  wp_auto. iPersist "c".
  destruct decide; first done.
  iMod (start_bag
    (λ v, ⌜v = Result.mk (query ++ "_primary.html"%go) true ∨
           v = Result.mk (query ++ "_secondary.html"%go) false⌝)%I
    _ c γc with "Hc_is_chan Hc_own") as "#Hch".
  { done. }
  iPersist "query".
  iPersist "c".

  (* Fork primary goroutine: always launched immediately. *)
  wp_apply wp_fork.
  { wp_auto.
    wp_apply (wp_GetPrimary query).
    wp_apply (wp_bag_send with "[$Hch]").
    { iPureIntro. left. done. }
    done. }

  (* time.After gives a handoff channel that fires after the hedge threshold. *)
  wp_apply wp_After.
  iIntros (hedge_ch γhedge) "#Hhedge".
  wp_auto_lc 5.

  (* First select: result on c | hedge threshold fires | done closes. *)
  wp_apply chan.wp_select_blocking. simpl.
  iSplit.
  { (* Branch 1: primary responded before hedge threshold. *)
    repeat iExists _; iSplitL ""; first done. iFrame "#".
    iApply (bag_recv_au with "[$] [$Hch]").
    iNext. iIntros (v) "%Hres". wp_auto.
    destruct Hres as [-> | ->].
    - iApply "HΦ". iLeft. iPureIntro;left;done.
    - iApply "HΦ". iLeft. iPureIntro;right;done.
  }
  iSplit.
  { (* Branch 2: hedge threshold fired — launch secondary, enter 2nd select. *)
    iExists time.Time.t, hedge_ch, γhedge.
    repeat iExists _. iSplitL ""; first done. iFrame "#".
    iSplitL "". { iApply is_bag_is_chan. done. }
    iApply (bag_recv_au with "[$] [$Hhedge]").
    iNext. iIntros (v) "_". wp_auto_lc 2.

    (* Fork secondary now that the hedge threshold has fired. *)
    wp_apply wp_fork.
    { wp_auto_lc 6.
      wp_apply (wp_GetSecondary query).
      wp_apply (wp_bag_send with "[$Hch]").
      { iPureIntro. right. done. }
      done.
    }

    (* Second select: result on c | done closes. *)
    wp_apply chan.wp_select_blocking. simpl.
    iSplit.
    { (* Branch 2a: primary or secondary result arrives. *)
      repeat iExists _; iSplitL ""; first done. iFrame "#".
      iApply (bag_recv_au with "[$] [$Hch]").
      iNext. iIntros (v0) "%Hres'". wp_auto_lc 4.
      destruct Hres' as [-> | ->].
      - iApply "HΦ". iLeft. iPureIntro;left;done.
      - iApply "HΦ". iLeft. iPureIntro;right;done.
    }
    { (* Branch 2b: done fired in second select. *)
      iSplitR ""; last done.
      iExists _, done_ch, γdone. repeat iExists _. iSplitL ""; first done.
      iFrame "#".
      iApply (closeable_chan_receive with "Hdone_closeable [HΦ errStr HerrStr]").
      { iIntros "[_ _]". wp_auto.
        iApply "HΦ". iRight. iFrame. iPureIntro. done. }
    }
  }
  { (* Branch 3: done fired in first select. *)
    iSplitR ""; last done.
    iExists _, done_ch, γdone. repeat iExists _. iSplitL ""; first done.
    iFrame "#".
    iApply (closeable_chan_receive with "Hdone_closeable [HΦ errStr HerrStr]").
    { iIntros "[_ _]". wp_auto.
      iApply "HΦ". iRight. iFrame. iPureIntro. done. }
  }
Qed.

End hedged_example.

Section hello_world.

Lemma wp_sys_hello_world :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.sys_hello_world #()
  {{{ RET #("Hello, World!"); True }}}.
Proof.
  wp_start. iApply "HΦ". done.
Qed.

Lemma wp_HelloWorldAsync :
  {{{ is_pkg_init chan_spec_raw_examples  }}}
    @! chan_spec_raw_examples.HelloWorldAsync #()
  {{{ (ch: loc)  (γfut: chan_names), RET #ch;
       is_chan ch γfut go_string ∗
  is_chan_bag (V:=go_string) γfut ch (λ (v : go_string), ⌜v = "Hello, World!"%go⌝)
    }}}.
Proof.
  wp_start. wp_auto.
  wp_apply chan.wp_make2; first done.
  iIntros (ch γ) "(#His_chan & Hcap & Hownchan)".
  wp_auto.
  iMod (start_bag (λ (v : go_string), ⌜v = "Hello, World!"%go⌝)%I
         _ ch γ with "His_chan Hownchan") as "#Hch".
  { done. }
  iPersist "ch".
  wp_apply (wp_fork).
  {
    wp_auto. wp_apply wp_sys_hello_world.
    iAssert (⌜"Hello, World!"%go = "Hello, World!"%go⌝)%I as "%HP";first done.
    wp_apply (wp_bag_send (V:=go_string) with "[$Hch]");done.
  }
  iApply "HΦ". iFrame "∗#".
Qed.

Lemma wp_HelloWorldSync :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.HelloWorldSync #()
  {{{ RET #("Hello, World!"); True }}}.
Proof.
  wp_start. wp_apply wp_HelloWorldAsync.
  iIntros (ch γfuture) "[#Hchan #Hfut]".
  wp_apply (wp_bag_receive with "Hfut").
  iIntros (v) "%Hv". wp_auto. subst v.
  iApply "HΦ". done.
Qed.

End hello_world.


Section cancellable.


Lemma wp_HelloWorldCancellable
  (done_ch : chan.t) (err_ptr1: loc) (err_msg: go_string)
  (γdone: chan_names) :
  {{{ is_pkg_init chan_spec_raw_examples ∗
        own_closeable_chan done_ch γdone (err_ptr1 ↦□ err_msg) closeable.Unknown }}}
    @! chan_spec_raw_examples.HelloWorldCancellable #done_ch #err_ptr1
    {{{
(result: go_string), RET #result;
      ⌜result = err_msg ∨ result = "Hello, World!"%go⌝
    }}}.
Proof.
  wp_start as "#Hdone_closeable".
  iDestruct (own_closeable_chan_is_chan with "Hdone_closeable") as "#Hdone_chan".
  wp_apply wp_alloc.
  iIntros (l). iIntros "Herr".
  wp_auto_lc 4. wp_apply wp_HelloWorldAsync.
  iIntros (ch γfuture) "[#Hch #Hfut]". wp_auto_lc 1.
  iFrame "#".
  wp_apply chan.wp_select_blocking. simpl.
  iSplit.
    {
      repeat iExists _; iSplitR; first done. iFrame "#".
      iApply (bag_recv_au with "[$] [$Hfut]").
      iNext. iIntros (v). iIntros "%Hw".
      wp_auto. subst v. iApply "HΦ". iPureIntro. right. done.
    }
    {
      iSplitL; last done. repeat iExists _; iSplitR; first done.
      iFrame "#".
      iApply (closeable_chan_receive with "Hdone_closeable [HΦ Herr]").
      {
        iIntros "[#HerrPtr _]". wp_auto. iApply "HΦ". iLeft. done.
      }
    }
Qed.


Lemma wp_HelloWorldWithTimeout :
  {{{ is_pkg_init chan_spec_raw_examples
  }}}
    @!  chan_spec_raw_examples.HelloWorldWithTimeout #()
  {{{ (result: go_string), RET #result;
      ⌜result = "Hello, World!"%go ∨
        result = "operation timed out"%go⌝
  }}}.
Proof.
  wp_start. wp_auto. wp_apply chan.wp_make1.
  iIntros (ch γ) "(#Hchan & _Hcap & Hoc)".
  rewrite -wp_fupd.
  wp_auto. iPersist "done".
  iMod (alloc_closeable_chan (errMsg_ptr ↦□ "operation timed out"%go) γ ch with "Hchan Hoc") as "Hown".
  iDestruct (own_closeable_chan_Unknown with "Hown") as "#Hdone_closeable".
  wp_apply (wp_fork with "[Hown errMsg done]").
  { wp_auto. wp_apply wp_Sleep.
    iPersist "errMsg".
    wp_apply (wp_closeable_chan_close (ty:=go.ChannelType go.sendrecv (go.StructType [])) with "[$Hown $errMsg]").
    iIntros "_". wp_auto. done.
  }

  wp_apply (wp_HelloWorldCancellable with "[$Hdone_closeable]").
  iIntros (result) "%Hres". wp_auto. iApply "HΦ".
  iPureIntro. destruct Hres; auto.
Qed.

End cancellable.

Section join.

Lemma wp_simple_join :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_pkg_init channel }}}
    @! chan_spec_raw_examples.simple_join #()
  {{{  RET #("Hello, World!"); True }}}.
Proof.
  wp_start. wp_auto_lc 3.
      iRename select (£1) into "Hlc".
  wp_apply chan.wp_make2; first done.
  iIntros (ch). iIntros (γ). iIntros "(#His_chan & _Hcap & Hownchan)".
  wp_auto.
  rewrite -fupd_wp.
  simpl.
  iMod (join.own_join_alloc_buff ch γ 1 with "His_chan Hownchan") as (γjoin) "[#Hisjoin Hjoin]".
  iMod ((join.join_alloc_worker γjoin ch
           emp%I ( message_ptr ↦ "Hello, World!"%go) 0)%I with "[$][$Hisjoin] [$Hjoin]")
    as "[Hjoin Hworker]".
  iModIntro. iPersist "ch".
  wp_apply (wp_fork with "[Hworker message]").
  {
    wp_auto.
    wp_apply (join.wp_join_send with "[$Hisjoin $Hworker $message]").
    { iFrame. }
  }
  wp_apply (join.wp_join_receive with "[$]").
  iIntros (v) "Hjoin".
  wp_auto.
  iMod (join.join_finish with "[$] [$] Hjoin") as "Hmsg".
  iMod (lc_fupd_elim_later with "[$][$Hmsg]") as "[_ Hmsg]".
  wp_auto.
  iApply "HΦ".
  done.
Qed.

Lemma wp_simple_multi_join :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_pkg_init channel }}}
    @! chan_spec_raw_examples.simple_multi_join #()
  {{{ RET #("Hello World"); True }}}.
Proof.
  wp_start. wp_auto_lc 3.
  iRename select (£1) into "Hlc1".
  wp_apply chan.wp_make2; first done.
  iIntros (ch γ) "(#His_chan & _Hcap & Hownchan)".
  wp_auto.
  rewrite -fupd_wp.
  simpl.
  iMod (join.own_join_alloc_buff ch γ 2 with "His_chan Hownchan") as (γjoin) "[#Hisjoin Hjoin]".
  iRename select (£1) into "Hlc2".
  iMod (join.join_alloc_worker γjoin ch emp (hello_ptr ↦ "Hello"%go) 0
        with "[$Hlc2] [$Hisjoin] [$Hjoin]") as "[Hjoin Hworker1]".
  iRename select (£1) into "Hlc3".
  iMod (join.join_alloc_worker γjoin ch
          (emp ∗ hello_ptr ↦ "Hello"%go) (world_ptr ↦ "World"%go) 1
        with "[$Hlc3] [$Hisjoin] [$Hjoin]") as "[Hjoin Hworker2]".
  iModIntro.
  iPersist "ch".
  wp_apply (wp_fork with "[Hworker1 hello]").
  {
    wp_auto.
    wp_apply (join.wp_join_send with "[$Hisjoin $Hworker1 $hello]").
    { iFrame. }
  }
  wp_apply (wp_fork with "[Hworker2 world]").
  {
    wp_auto.
    wp_apply (join.wp_join_send with "[$Hisjoin $Hworker2 $world]").
    { iFrame. }
  }
  wp_apply (join.wp_join_receive with "[$Hjoin $Hisjoin]").
  iIntros (v1) "Hjoin".
  wp_auto_lc 3.
  wp_apply (join.wp_join_receive with "[$Hjoin $Hisjoin]").
  iIntros (v2) "Hjoin".
  wp_auto_lc 1.
  iRename select (£1) into "Hlc4".
  iMod (join.join_finish with "[$Hlc4] [$Hisjoin] Hjoin") as "Hboth".
  iMod (lc_fupd_elim_later with "[$] [$Hboth]") as "[[_ Hhello] Hworld]".
  wp_auto.
  iApply "HΦ". done.
Qed.

End join.

Section exchange_pointer_proof.

Lemma wp_exchangePointer :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.exchangePointer #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto. wp_apply chan.wp_make1.
  iIntros (ch γ) "(#His_ch & % & Hch)". wp_auto. simpl.
  iMod (start_handshake _ (λ _, x_ptr ↦ W64 1)%I (y_ptr ↦ W64 2)%I with "[$] [$]") as "#H".
  iPersist "ch".
  wp_apply (wp_fork with "[x]").
  - wp_auto. by wp_apply (wp_handshake_send with "[$H $x]") as "y".
  - wp_apply (wp_handshake_receive with "[$H $y]") as "* x". by iApply "HΦ".
Qed.

End exchange_pointer_proof.

Section broadcast_example_proof.

Lemma wp_BroadcastExample :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.BroadcastExample #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  wp_apply (chan.wp_make1).
  iIntros (done_ch γdone) "(#Hdone_is_chan & _ & Hdone_own)". wp_auto. simpl.
  wp_apply (chan.wp_make1).
  iIntros (result1_ch γr1) "(#Hr1_is_chan & _ & Hr1_own)". wp_auto. simpl.
  wp_apply (chan.wp_make1).
  iIntros (result2_ch γr2) "(#Hr2_is_chan & _ & Hr2_own)". wp_auto. simpl.
  iMod (start_bag (λ v, ⌜v = W64 6⌝)%I with "Hr1_is_chan Hr1_own")
    as "#Hbag1".
  { done. }
  iMod (start_bag (λ v, ⌜v = W64 10⌝)%I with "Hr2_is_chan Hr2_own")
    as "#Hbag2".
  { done. }
  iMod (alloc_closeable_chan (sharedValue_ptr ↦□ W64 2)%I γdone done_ch with "Hdone_is_chan Hdone_own") as "Hown_done".
  iDestruct (own_closeable_chan_Unknown with "Hown_done") as "#Hdone_closeable".
  iPersist "done result1 result2".
  wp_apply (wp_fork with "[result1 result2 done]").
  {
    rename done_ch into done_ch_1. wp_auto_lc 1.
    wp_apply (chan.wp_receive done_ch_1 γdone with "Hdone_is_chan").
    iIntros "(?&?&?&?)".
    iApply (closeable_chan_receive with "Hdone_closeable").
    iIntros "[#HShared _]". wp_auto.
    wp_apply (wp_bag_send with "[$Hbag1]"); word.
  }
   wp_apply (wp_fork with "[result1 result2 done]").
  {
    rename done_ch into done_ch_1.
    wp_auto_lc 1.
    wp_apply (chan.wp_receive done_ch_1 γdone with "Hdone_is_chan").
    iIntros "(?&?&?&?)".
    iApply (closeable_chan_receive with "Hdone_closeable").
    iIntros "[#HShared _]". wp_auto.
    wp_apply (wp_bag_send with "[$Hbag2]"); word.
  }
  iPersist "sharedValue".
  wp_apply (wp_closeable_chan_close (ty:=go.ChannelType go.sendrecv (go.StructType [])) with "[$Hown_done $sharedValue]").
  iIntros "_". wp_auto.
  wp_apply (wp_bag_receive with "Hbag1").
  iIntros (v1) "%Hv1". subst v1. wp_auto.
  wp_apply (wp_bag_receive with "Hbag2"). iIntros (v2) "%Hv2".
  subst v2. wp_auto. by iApply "HΦ".
  Unshelve. all: try apply _. all: try exact sem.
Qed.

End broadcast_example_proof.
End proof.
