From New.proof.github_com.mit_pdos.perennial.goose.testdata.examples Require Import channel_examples_init.
From New.golang.theory.chan.idioms
  Require Import base bag handshake broadcast future.
From New.proof Require Import strings time sync.
From New.golang Require Import theory.
From New.proof Require Import strings.
From New.code Require Import github_com.mit_pdos.perennial.goose.testdata.examples.channel.
Import channel_examples.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : channel_examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Section hedged_example.

Lemma wp_GetPrimary (q : go_string) :
  {{{ is_pkg_init channel_examples }}}
    @! channel_examples.GetPrimary #q
  {{{ RET #(q ++ "_primary.html"%go); True }}}.
Proof. wp_start. wp_auto. iApply "HΦ". done. Qed.

Lemma wp_GetSecondary (q : go_string) :
  {{{ is_pkg_init channel_examples }}}
    @! channel_examples.GetSecondary #q
  {{{ RET #(q ++ "_secondary.html"%go); True }}}.
Proof. wp_start. wp_auto. iApply "HΦ". done. Qed.

Lemma wp_CancellableHedgedRequest (query : go_string)
    (hedgeThreshold : time.Duration.t)
    (errStr_ptr' : loc)
    (done_ch : chan.t) (γdone : chan_names) :
  {{{ is_pkg_init channel_examples ∗
      own_broadcast_chan done_ch γdone True broadcast.Unknown ∗
      errStr_ptr' ↦ ""%go }}}
    @! channel_examples.CancellableHedgedRequest
         #query #hedgeThreshold #errStr_ptr' #done_ch
  {{{ (v : go_string) (b : bool),
      RET #(channel_examples.Result.mk v b);
      (* Primary won. *)
      ⌜(v = query ++ "_primary.html"%go ∧ b = true) ∨
      (* Hedged request won. *)
       (v = query ++ "_secondary.html"%go ∧ b = false)⌝ ∨
      (* Done channel closed before any result arrived — caller wrote
         "cancelled" into errStr_ptr' and we return the zero Result.  *)
      (errStr_ptr' ↦ "cancelled"%go ∗ ⌜v = ""%go ∧ b = false⌝) }}}.
Proof.
  wp_start as "(#Hdone_broadcast & HerrStr)".
  iDestruct (own_broadcast_chan_is_chan with "Hdone_broadcast") as "#Hdone_chan".
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
      iApply (broadcast_chan_receive with "Hdone_broadcast [HΦ errStr HerrStr]").
      { iIntros "[_ _]". wp_auto.
        iApply "HΦ". iRight. iFrame. iPureIntro. done. }
    }
  }
  { (* Branch 3: done fired in first select. *)
    iSplitR ""; last done.
    iExists _, done_ch, γdone. repeat iExists _. iSplitL ""; first done.
    iFrame "#".
    iApply (broadcast_chan_receive with "Hdone_broadcast [HΦ errStr HerrStr]").
    { iIntros "[_ _]". wp_auto.
      iApply "HΦ". iRight. iFrame. iPureIntro. done. }
  }
Qed.

End hedged_example.

Section hello_world.

Lemma wp_sys_hello_world :
  {{{ is_pkg_init channel_examples }}}
    @! channel_examples.sys_hello_world #()
  {{{ RET #("Hello, World!"); True }}}.
Proof.
  wp_start. iApply "HΦ". done.
Qed.

Lemma wp_HelloWorldAsync :
  {{{ is_pkg_init channel_examples  }}}
    @! channel_examples.HelloWorldAsync #()
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
  {{{ is_pkg_init channel_examples }}}
    @! channel_examples.HelloWorldSync #()
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
  {{{ is_pkg_init channel_examples ∗
        own_broadcast_chan done_ch γdone (err_ptr1 ↦□ err_msg) broadcast.Unknown }}}
    @! channel_examples.HelloWorldCancellable #done_ch #err_ptr1
    {{{
(result: go_string), RET #result;
      ⌜result = err_msg ∨ result = "Hello, World!"%go⌝
    }}}.
Proof.
  wp_start as "#Hdone_broadcast".
  iDestruct (own_broadcast_chan_is_chan with "Hdone_broadcast") as "#Hdone_chan".
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
      iApply (broadcast_chan_receive with "Hdone_broadcast [HΦ Herr]").
      {
        iIntros "[#HerrPtr _]". wp_auto. iApply "HΦ". iLeft. done.
      }
    }
Qed.


Lemma wp_HelloWorldWithTimeout :
  {{{ is_pkg_init channel_examples
  }}}
    @!  channel_examples.HelloWorldWithTimeout #()
  {{{ (result: go_string), RET #result;
      ⌜result = "Hello, World!"%go ∨
        result = "operation timed out"%go⌝
  }}}.
Proof.
  wp_start. wp_auto. wp_apply chan.wp_make1.
  iIntros (ch γ) "(#Hchan & _Hcap & Hoc)".
  rewrite -wp_fupd.
  wp_auto. iPersist "done".
  iMod (alloc_broadcast_chan (errMsg_ptr ↦□ "operation timed out"%go) γ ch with "Hchan Hoc") as "Hown".
  iDestruct (own_broadcast_chan_Unknown with "Hown") as "#Hdone_broadcast".
  wp_apply (wp_fork with "[Hown errMsg done]").
  { wp_auto. wp_apply wp_Sleep.
    iPersist "errMsg".
    wp_apply (wp_broadcast_chan_close (ty:=go.ChannelType go.sendrecv (go.StructType [])) with "[$Hown $errMsg]").
    iIntros "_". wp_auto. done.
  }

  wp_apply (wp_HelloWorldCancellable with "[$Hdone_broadcast]").
  iIntros (result) "%Hres". wp_auto. iApply "HΦ".
  iPureIntro. destruct Hres; auto.
Qed.

End cancellable.

Section join.
Set Default Proof Using "All".

Lemma wp_simple_join :
  {{{ is_pkg_init channel_examples ∗ is_pkg_init channel }}}
    @! channel_examples.simple_join #()
  {{{  RET #("Hello, World!"); True }}}.
Proof.
  wp_start. wp_auto_lc 3.
  wp_apply chan.wp_make2; first done.
  iIntros (ch γ) "(#His_chan & _Hcap & Hownchan)".
  wp_auto.
  rewrite -fupd_wp.
  simpl.
  iMod (start_future (V:=unit) (t:=go.StructType []) ch γ (chanstate.Buffered []) with "His_chan Hownchan")
    as (γfut) "[#Hisfut HAwait]".
  { right. done. }
  iMod (future_alloc_promise (V:=unit) (t:=go.StructType []) γfut ch (fun _ : unit => (message_ptr ↦ "Hello, World!"%go))%I []
        with "Hisfut HAwait") as "[Hpromise HAwait]".
  iModIntro. iPersist "ch".
  wp_apply (wp_fork with "[Hpromise message]").
  {
    wp_auto.
    wp_apply (wp_future_fulfill (V:=unit) (t:=go.StructType []) with "[$Hisfut $Hpromise $message]").
    done.
  }
  wp_apply (wp_future_await (V:=unit) (t:=go.StructType []) with "[$Hisfut $HAwait]").
  iIntros (v P pre post) "(%Hsplit & HP & _)".
  destruct pre; simpl in Hsplit; [injection Hsplit as <- | exfalso; by destruct pre].
  destruct post; [|done].
  wp_auto.
  iApply "HΦ". done.
Qed.

Lemma wp_simple_multi_join :
  {{{ is_pkg_init channel_examples ∗ is_pkg_init channel }}}
    @! channel_examples.simple_multi_join #()
  {{{ RET #("Hello World"); True }}}.
Proof.
  wp_start. wp_auto_lc 3.
  wp_apply chan.wp_make2; first done.
  iIntros (ch γ) "(#His_chan & _Hcap & Hownchan)".
  wp_auto.
  rewrite -fupd_wp.
  simpl.
  iMod (start_future (V:=unit) (t:=go.StructType []) ch γ (chanstate.Buffered []) with "His_chan Hownchan")
    as (γfut) "[#Hisfut HAwait]".
  { right. done. }
  iMod (future_alloc_promise (V:=unit) (t:=go.StructType []) γfut ch (fun _ : unit => (hello_ptr ↦ "Hello"%go))%I []
        with "Hisfut HAwait") as "[Hpromise1 HAwait]".
  iMod (future_alloc_promise (V:=unit) (t:=go.StructType []) γfut ch (fun _ : unit => (world_ptr ↦ "World"%go))%I
          [(fun _ : unit => (hello_ptr ↦ "Hello"%go))%I]
        with "Hisfut HAwait") as "[Hpromise2 HAwait]".
  iModIntro.
  iPersist "ch".
  wp_apply (wp_fork with "[Hpromise1 hello]").
  {
    wp_auto.
    wp_apply (wp_future_fulfill (V:=unit) (t:=go.StructType []) with "[$Hisfut $Hpromise1 $hello]").
    done.
  }
  wp_apply (wp_fork with "[Hpromise2 world]").
  {
    wp_auto.
    wp_apply (wp_future_fulfill (V:=unit) (t:=go.StructType []) with "[$Hisfut $Hpromise2 $world]").
    done.
  }
  wp_apply (wp_future_await (V:=unit) (t:=go.StructType []) with "[$Hisfut $HAwait]").
  iIntros (v1 P1 pre1 post1) "(%Hsplit1 & HP1 & HAwait)".
  (* Resolve which contract was fulfilled first *)
  destruct pre1 as [|? pre1']; simpl in Hsplit1;
    [ injection Hsplit1 as ? Hpost1; subst P1 post1; simpl in *
    | destruct pre1' as [|? pre1'']; simpl in Hsplit1;
      [ injection Hsplit1 as ? ? Hpost1; subst; simpl in *
      | exfalso; by destruct pre1'' ]];
  wp_auto_lc 3;
  wp_apply (wp_future_await (V:=unit) (t:=go.StructType []) with "[$Hisfut $HAwait]");
  iIntros (v2 P2 pre2 post2) "(%Hsplit2 & HP2 & _)";
  (destruct pre2 as [|? pre2']; simpl in Hsplit2;
    [ injection Hsplit2 as ? Hpost2; subst P2 post2; simpl in *
    | exfalso; by destruct pre2' ]);
  wp_auto;
  iApply "HΦ"; done.
Qed.

End join.

Section exchange_pointer_proof.

Lemma wp_exchangePointer :
  {{{ is_pkg_init channel_examples }}}
    @! channel_examples.exchangePointer #()
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
  {{{ is_pkg_init channel_examples }}}
    @! channel_examples.BroadcastExample #()
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
  iMod (alloc_broadcast_chan (sharedValue_ptr ↦□ W64 2)%I γdone done_ch with "Hdone_is_chan Hdone_own") as "Hown_done".
  iDestruct (own_broadcast_chan_Unknown with "Hown_done") as "#Hdone_broadcast".
  iPersist "done result1 result2".
  wp_apply (wp_fork with "[result1 result2 done]").
  {
    rename done_ch into done_ch_1. wp_auto_lc 1.
    wp_apply (chan.wp_receive done_ch_1 γdone with "Hdone_is_chan").
    iIntros "(?&?&?&?)".
    iApply (broadcast_chan_receive with "Hdone_broadcast").
    iIntros "[#HShared _]". wp_auto.
    wp_apply (wp_bag_send with "[$Hbag1]"); word.
  }
   wp_apply (wp_fork with "[result1 result2 done]").
  {
    rename done_ch into done_ch_1.
    wp_auto_lc 1.
    wp_apply (chan.wp_receive done_ch_1 γdone with "Hdone_is_chan").
    iIntros "(?&?&?&?)".
    iApply (broadcast_chan_receive with "Hdone_broadcast").
    iIntros "[#HShared _]". wp_auto.
    wp_apply (wp_bag_send with "[$Hbag2]"); word.
  }
  iPersist "sharedValue".
  wp_apply (wp_broadcast_chan_close (ty:=go.ChannelType go.sendrecv (go.StructType [])) with "[$Hown_done $sharedValue]").
  iIntros "_". wp_auto.
  wp_apply (wp_bag_receive with "Hbag1").
  iIntros (v1) "%Hv1". subst v1. wp_auto.
  wp_apply (wp_bag_receive with "Hbag2"). iIntros (v2) "%Hv2".
  subst v2. wp_auto. by iApply "HΦ".
  Unshelve. all: try apply _. all: try exact sem.
Qed.

End broadcast_example_proof.
End proof.
