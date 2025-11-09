From New.proof Require Export proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Import protocol.base simple future spsc done dsp dsp_proofmode mpmc join.
From New.proof Require Import strings time sync.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.
From iris.base_logic Require Import ghost_map.
From New.golang.theory Require Import struct string chan.
From iris.algebra Require Import gmultiset.

Import chan_spec_raw_examples.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf chan_spec_raw_examples := build_get_is_pkg_init_wf.
Instance stream_countable : Countable stream.t.
Proof.
  refine (inj_countable'
           (λ x, (stream.req' x, stream.res' x, stream.f' x))
          (λ '(a, b, c), stream.mk a b c) _).
  by intros [].
Defined.

Section hello_world.
Context `{!chan_protocolG Σ go_string}.

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
  {{{ (ch: loc) (γfuture: future_names), RET #ch; is_future (V:=go_string) (t:=stringT) γfuture ch
        (λ (v : go_string), ⌜v = "Hello, World!"%go⌝)  ∗
      await_token γfuture }}}.
Proof.
  wp_start. wp_auto.
  wp_apply chan.wp_make; first done.
  iIntros (ch). iIntros (γ). iIntros "(#HisChan & Hcap & Hownchan)".
  wp_auto.
  simpl in *.
  iDestruct ((start_future (V:=go_string) ch (λ v, ⌜ v = "Hello, World!"%go ⌝%I) γ) with "[$HisChan] [$Hownchan]") as ">(%γfuture & Hfut)".
  iDestruct "Hfut" as "(#Hisfut & Hawait & Hfulfill)".
  iPersist "ch".
  wp_apply (wp_fork with "[Hfulfill]").
  {
    wp_auto.
    wp_apply wp_sys_hello_world.
    iAssert (⌜"Hello, World!"%go = "Hello, World!"%go⌝)%I as "HP".
    { iPureIntro. reflexivity. }
    wp_apply (chan.wp_send with "[]") as "[Hlc _]".
    { iDestruct (future_is_channel with "Hisfut") as "$". }
  iApply (future_fulfill_au γfuture ch (λ v : go_string, ⌜v = "Hello, World!"%go⌝%I) "Hello, World!"%go
  with "[$] [$]").
    iIntros "!> _".
    wp_auto.
    done.
  }
  iApply "HΦ".
  iFrame "∗#".
Qed.

Lemma wp_HelloWorldSync :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.HelloWorldSync #()
  {{{ RET #("Hello, World!"); True }}}.
Proof using chan_protocolG0.
  wp_start.
  wp_apply wp_HelloWorldAsync.
  iIntros (ch γfuture) "[#Hfut Hawait]".
  wp_apply (chan.wp_receive) as "[Hlc _]".
  { iApply future_is_channel; done. }
  iApply (future_await_au (V:=go_string) (t:=stringT)  γfuture ch
               (λ (v : go_string), ⌜v = "Hello, World!"%go⌝%I) with "[$] [$Hawait $Hlc]").
  iIntros "!> %v %Heq". subst.
  wp_auto.
  iApply "HΦ".
  done.
Qed.

End hello_world.


Section cancellable.
Context `{!chan_protocolG Σ unit}.
Context `{!chan_protocolG Σ go_string}.

Lemma wp_HelloWorldCancellable
  (done_ch : loc) (err_ptr1: loc) (err_msg: go_string)
  (γdone: done_names) :
  {{{ is_pkg_init chan_spec_raw_examples ∗
        is_done (V:=unit) (t:=structT []) γdone done_ch ∗
        Notified (V:=unit) γdone (err_ptr1 ↦ err_msg)  }}}
    @! chan_spec_raw_examples.HelloWorldCancellable #done_ch #err_ptr1
    {{{
(result: go_string), RET #result;
      ⌜result = err_msg ∨ result = "Hello, World!"%go⌝
    }}}.
Proof using chan_protocolG0 chan_protocolG1.

  wp_start. wp_apply wp_alloc.
  iIntros (l). iIntros "Herr".
  wp_auto_lc 4.
  wp_apply wp_HelloWorldAsync.
  iIntros (ch γfuture) "[#Hfut Hawait]". wp_auto_lc 1.
  iDestruct "Hpre" as "(#H1 & H2)".
  iAssert ( is_channel (t:=structT []) done_ch γdone.(chan_name)) as "#Hdonech".
  {
    iFrame "#".
    unfold is_done.
    iDestruct "H1" as "[#Hdone #Hinv]". iFrame "#".

  }
  iDestruct "Hfut" as "[#Hfut #Hinv1]". iFrame "#".
  wp_apply chan.wp_select_blocking.
  simpl.
    iSplit.
    {
      iFrame "Hfut".
      iRename select (£1) into "Hlc".
      iApply ((future_await_au (V:=go_string) γfuture ch   )
               with " [$Hfut $Hinv1] [$Hawait $Hlc]").
      iNext. iIntros (v). iIntros "%Hw".
      wp_auto.
      subst v.
      iApply "HΦ".
      iPureIntro.
      right. done. }
    {
      iFrame "Hdonech".

      iApply ((done_receive_au (V:=unit) γdone done_ch  (err_ptr1 ↦ err_msg)%I )
               with " [$H1] [H2] [HΦ Herr] [$]").
      {
        iFrame.
       }
       {

        iNext. iIntros "Herr'".
      wp_auto. iApply "HΦ". iLeft. done.
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
  Proof using chan_protocolG0 chan_protocolG1.
  wp_start.
  wp_auto.
  wp_apply (chan.wp_make (t:=structT [])); first done.
  iIntros (ch γ) "(#Hchan & _Hcap & Hoc)".
  simpl.
  iDestruct (start_done ch γ with "Hchan") as "Hstart".
iMod ("Hstart" with "Hoc") as (γdone) "(#Hdone & Hnot)".
wp_auto.
iPersist "done".

iMod (done_alloc_notified (t:=structT []) γdone ch True (errMsg_ptr ↦ "operation timed out"%go)%I
      with "[$Hdone] [$Hnot]") as "[HNotify HNotified]".
wp_apply (wp_fork with "[HNotify errMsg done]").
{ wp_auto.
  wp_apply wp_Sleep.
  wp_apply (chan.wp_close (V:=()) with "[]") as "(Hlc1 & Hlc2 & Hlc3 & _)".
  { iApply (done_is_channel with "Hdone"). }
  iApply (done_close_au (V:=()) with "[$] [$] [$HNotify errMsg]").
  { iFrame. }
  iNext.
  wp_auto.
  done. }

wp_apply (wp_HelloWorldCancellable with "[$Hdone $HNotified][HΦ]").
{
  iIntros (result).
  iIntros "%Hres".
  wp_auto.
  iApply "HΦ".
  iPureIntro. destruct Hres; auto. }
Qed.

End cancellable.


Section fibonacci_examples.
Context `{!chan_protocolG Σ w64}.

Fixpoint fib (n: nat) : w64 :=
  match n with
  | 0%nat => W64 0
  | 1%nat => W64 1
  | S (S n' as n'') => word.add (fib n'') (fib n')
  end.

Definition fib_list (n: nat) : list w64 :=
  map fib (seq 0 n).

Lemma fib_list_succ (n: nat) :
  fib_list (S n) = fib_list n ++ [fib n].
Proof.
  unfold fib_list.
  rewrite seq_S.
  rewrite map_app.
  simpl. reflexivity.
Qed.

Lemma fib_list_length (n: nat) :
  length (fib_list n) = n.
Proof.
  unfold fib_list.
  rewrite map_length.
  apply seq_length.
Qed.

Lemma fib_succ (k:nat) :
  fib (S k) =
    match k with 0%nat => W64 1 | S k' => word.add (fib (S k')) (fib k') end.
Proof. destruct k; simpl; reflexivity. Qed.

Open Scope Z_scope.

Lemma wp_fibonacci (n: w64) (c_ptr: loc) γ:
  0 < sint.Z n < 2^63 →
  {{{ is_pkg_init chan_spec_raw_examples ∗

      is_spsc γ c_ptr (λ i v, ⌜v = fib (Z.to_nat i)⌝)
                  (λ sent, ⌜sent = fib_list  (sint.nat n)⌝) ∗
      spsc_producer γ []
  }}}
    @! chan_spec_raw_examples.fibonacci #n #c_ptr
  {{{ RET #(); True }}}.
Proof.
  intros Hn.
  wp_start.
  iDestruct "Hpre" as "(#Hspsc & Hprod)".
  rename c_ptr into c_ptr0.
  wp_alloc_auto.
  wp_auto.

 iAssert (∃ (i: nat) (sent: list w64),
           "Hprod" ∷ spsc_producer γ sent ∗
           "x"     ∷ x_ptr ↦ fib i ∗
           "y"     ∷ y_ptr ↦ fib (S i) ∗
           "i"     ∷ i_ptr ↦ W64 i ∗
           "c"     ∷ c_ptr ↦ c_ptr0 ∗
           "%Hil"  ∷ ⌜i = length sent⌝ ∗
           "%Hsl"  ∷ ⌜sent = fib_list i⌝ ∗
           "%Hi"   ∷ ⌜0 ≤ i ≤ sint.Z n⌝)%I
  with "[x y i c Hprod]" as "IH".
{
  iFrame.
  iExists 0%nat.
  iFrame.
  iPureIntro. simpl. unfold fib_list.
  simpl.
  split;first done.
  split;first done.
  lia.
}

    wp_for "IH".
  wp_if_destruct.
  {

     wp_apply (wp_spsc_send (V:=w64) (t:=intT) γ c_ptr0
             (λ (i : Z) (v : w64), ⌜v = fib (Z.to_nat i)⌝%I)
              (λ sent0 : list w64, ⌜sent0 = fib_list (sint.nat n)⌝%I) sent

              with "[ Hspsc Hprod]").
     { iFrame "#".  iFrame.  simpl.
       replace (Z.to_nat (length sent)) with (length sent) by lia.
       word.
       }
     iIntros "Hprod".
     wp_auto.
     wp_for_post.
     iFrame.
      iExists ((length sent) + 1)%nat.
      iFrame.

      iFrame.
      replace (length sent + 1)%nat with (S (length sent)) by lia.
      destruct (length sent) eqn: H.
      {
        iFrame.  iPureIntro. rewrite app_length.  rewrite H. simpl. unfold fib_list. simpl.
        split;first done.
        rewrite Hsl.
        split;first done.
        lia.
      }
      iFrame.

(* y: turn the add(...) form into fib (S (length sent + 1)) *)
     (* add (fib (S k)) (fib k) → fib (S (S k)) *)
    replace   (w64_word_instance.(word.add)
                  (fib (S n0))
                  (w64_word_instance.(word.add)
                     (fib (S n0))
                     (fib n0)))
                with  (fib (S (S (S n0)))).
    {
      iFrame.
      replace ( w64_word_instance.(word.add) (W64 (S n0)) (W64 1)) with (W64 (S (S n0))).
      {
        iFrame. iPureIntro.
        split.
        { rewrite length_app.  rewrite singleton_length.  rewrite H. lia.
          }
          split.
        {


          subst sent.
          rewrite <- fib_list_succ.
          done.

      }
      {
        word.
      }
    }
    {
      word.
    }
    }
    {
      rewrite fib_succ.
      rewrite fib_succ.
      word.
    }
    }
    {
    wp_apply (wp_spsc_close (V:=w64) (t:=intT) γ c_ptr0
             (λ (i : Z) (v : w64), ⌜v = fib (Z.to_nat i)⌝%I)
              (λ sent0 : list w64, ⌜sent0 = fib_list (sint.nat n)⌝%I) sent

              with "[ $Hspsc $Hprod]").
    { iFrame "#".   iPureIntro. rewrite Hsl.
      assert ((length sent) = sint.nat n).
      {
       assert (length sent < 2^64). { lia. }

       word.
      }
 destruct (length sent) eqn: H1.
      { word.

      }
      rewrite H. done.
        }
    iApply "HΦ". done.
}
Qed.

Lemma wp_fib_consumer:
  {{{ is_pkg_init chan_spec_raw_examples
  }}}
   @! chan_spec_raw_examples.fib_consumer #()
  {{{ sl, RET #(sl);
      sl ↦* (fib_list 10)


  }}}.
Proof using chan_protocolG0.
  wp_start. wp_auto.
  wp_apply (chan.wp_make); first done.
  iIntros (c γ) "(#Hchan & %Hcap_eq & Hown)".
  wp_auto.
  simpl.
   iMod (start_spsc c (λ i v, ⌜v = fib (Z.to_nat i)⌝%I)
                  (λ sent, ⌜sent = fib_list 10 ⌝%I)  γ
    with "[Hchan] [Hown]") as (γspsc) "(#Hspsc & Hprod & Hcons)".
   {
      iFrame "#".
   }
   {
     iFrame.
     }
  wp_apply (chan.wp_cap with "[$Hchan]").
  wp_apply (wp_fork with "[Hprod]").
   {

   wp_apply ((wp_fibonacci) with "[$Hprod]").
   {
     word.
   }
   {
     iFrame "#".
     replace (sint.nat (W64 (γ.(chan_cap)))) with 10%nat by word.
     iFrame "#".
   }
   done.
   }
  iDestruct (theory.slice.own_slice_nil  (DfracOwn 1)) as "Hnil".
   iDestruct (theory.slice.own_slice_cap_nil (V:=w64)) as "Hnil_cap".
   simpl.
 iAssert (∃ (i: nat) (i_v: w64) sl,
             "i" ∷ i_ptr ↦ i_v ∗
            "c"  ∷ c_ptr ↦ c ∗
  "Hcons"  ∷ spsc_consumer γspsc (fib_list i) ∗
  "Hsl"  ∷ sl ↦* (fib_list i) ∗
  "results"  ∷ results_ptr ↦ sl ∗
  "oslc"  ∷ theory.slice.own_slice_cap w64 sl (DfracOwn 1)
)%I
  with "[ i c Hcons results]" as "IH".
{
  iExists 0%nat.
  iFrame.
  unfold fib_list. iFrame "#".
}


  rewrite /chan.for_range.
  wp_auto.
  wp_for "IH".
   wp_apply ((wp_spsc_receive (t:=intT) γspsc c γspsc (λ i v, ⌜v = fib (Z.to_nat i)⌝%I)
                  (λ sent, ⌜sent = fib_list 10 ⌝%I) (fib_list i) _) with "[Hcons]").
   { iFrame "#".  iFrame.   }
   iIntros (v ok).
   destruct ok.
   {
     iIntros "[%Hfib Hcons]".


      wp_auto.
      iDestruct (slice.own_slice_len with "Hsl") as "[%Hl %Hcap]".
      iDestruct (slice.own_slice_len with "Hsl") as "[%Hlen_slice %Hslgtz]".


wp_apply wp_slice_literal. iIntros (sl0) "Hsl0".
      iDestruct (slice.own_slice_len with "Hsl0") as "[%Hl0 %Hcap0]".
      iDestruct (slice.own_slice_len with "Hsl0") as "[%Hlen_slice0 %Hslgtz0]".
wp_auto.
wp_apply (wp_slice_append (t:=intT)
          sl (fib_list i)
          sl0 [v]
          (DfracOwn 1)
          with "[$Hsl $Hsl0 $oslc ]").

     iIntros (sl') "Hsl'".
     wp_auto.
     wp_for_post.
     iFrame.
     iExists (S i).
     iDestruct "Hsl'" as "(Hsl & Hcap3 & Hsl0)".
     rewrite Hfib.
     iFrame.
iSplitL "Hcons".
{
  rewrite fib_list_length.
  rewrite Nat2Z.id.
  rewrite <- fib_list_succ.
  iFrame.
}
{
  rewrite fib_list_length.
  rewrite Nat2Z.id.
  rewrite <- fib_list_succ.
  iFrame.
}
}
iIntros "%Hfl". wp_auto. wp_for_post. iFrame.
   iApply "HΦ".
   rewrite Hfl. iFrame "Hsl".
Qed.

End fibonacci_examples.

Section dsp_examples.
Context `{!chan_protocolG Σ interface.t}.
Context `{!dspG Σ interface.t}.

Definition ref_prot : iProto Σ interface.t :=
  <! (l:loc) (x:Z)> MSG (interface.mk (ptrT.id intT.id) #l) {{ l ↦ W64 x }} ;
  <?> MSG (interface.mk (structT.id []) #()) {{ l ↦ w64_word_instance.(word.add) (W64 x) (W64 2) }} ;
  END.
Lemma wp_DSPExample :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.DSPExample #()
  {{{ RET #(W64 42); True }}}.
Proof using chan_protocolG0 globalsGS0 dspG0.
  wp_start. wp_auto.
  wp_apply (chan.wp_make (V:=interface.t) (t:=interfaceT) 0); [done|].
  iIntros (c γ) "(#Hic & _Hcap & Hoc)". wp_auto.
  wp_apply (chan.wp_make (V:=interface.t) (t:=interfaceT) 0); [done|].
  iIntros (signal γ') "(#Hicsignal & _Hcapsignal & Hocsignal)". wp_auto.
  iMod (dsp_session_init _ _ _ _ _ _ _ ref_prot with "Hic Hicsignal Hoc Hocsignal")
                       as "[Hc Hcsignal]";
    [by eauto|by eauto|..].
  iPersist "c signal".
  wp_apply (wp_fork with "[Hcsignal]").
  { wp_auto.
    wp_recv (l x) as "Hl".
    wp_auto.
    wp_apply wp_interface_type_assert; [done|].
    wp_send with "[$Hl]".
    by wp_auto. }
  wp_send with "[$val]".
  wp_auto.
  wp_recv as "Hl".
  wp_auto. by iApply "HΦ".
Qed.

End dsp_examples.

Section select_panic.
Context `{!chan_protocolG Σ unit}.

(** Invariant: channel must be Idle, all other states are False *)
Definition is_select_nb_only (γ : chan_names) (ch : loc) : iProp Σ :=
  "#Hch" ∷ is_channel (V:=unit)  ch γ ∗
  "#Hinv" ∷ inv nroot (
    ∃ (s : chan_rep.t unit),
      "Hoc" ∷ own_channel  ch s γ ∗
      match s with
      | chan_rep.Idle => True
      | _ => False
      end
  ).


(** Create the idiom from a channel in Idle state *)
Lemma start_select_nb_only (ch : loc) (γ : chan_names) :
  is_channel ch γ -∗
  own_channel ch chan_rep.Idle γ ={⊤}=∗
  ∃ γnb, is_select_nb_only γnb ch.
Proof.
  iIntros "#Hch Hoc".
  iMod (inv_alloc nroot with "[Hoc]") as "$".
  { iNext. iFrame. }
  simpl.
  by iFrame "#".
  Qed.

(** Nonblocking send AU - vacuous since we ban all send preconditions *)
Lemma select_nb_only_send_au γ ch v  :
  ∀ Φ,
  is_select_nb_only γ ch -∗
  ( False -∗  Φ) -∗
         £1 ∗ £1 -∗
  send_au_fast ch v γ Φ.
Proof.
   intros Φ.
  iIntros "#Hnb".
  iIntros "HΦ".
  iIntros "[Hlc1 Hlc2]".
  iNamed "Hnb".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  destruct s; try done.
  (* Only Idle case remains - all others give False from invariant *)
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext.
  iFrame.
  Qed.



(** Nonblocking receive AU - vacuous since we ban all receive preconditions *)
Lemma select_nb_only_rcv_au γ ch :
   ∀ (Φ: unit → bool → iProp Σ),
  is_select_nb_only  γ ch -∗
  ( ∀ (v:unit), False -∗ Φ v true) -∗
         £1 ∗ £1 -∗
  rcv_au_fast ch γ (λ (v:unit) (ok:bool), Φ v ok).
Proof.
  intros Φ.
  iIntros "#Hnb".
  iIntros "HΦ".
  iIntros "[Hlc1 Hlc2]".
  iNamed "Hnb".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  destruct s; try done.
  (* Only Idle case remains - all others give False from invariant *)
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext.
  iFrame.
Qed.


Lemma wp_select_nb_no_panic :
  {{{ is_pkg_init chan_spec_raw_examples}}}
    @! chan_spec_raw_examples.select_nb_no_panic #()
  {{{ RET #(); True }}}.
  wp_start. wp_auto_lc 2.
  wp_apply chan.wp_make. { done. }
  iIntros (ch). iIntros (γ). iIntros "(#HisChan & _Hcap & Hownchan)".
  iRename select (£1) into "Hlc1".
  wp_auto_lc 2.
  iRename select (£1) into "Hlc2".
  simpl.
  iPersist "ch".
  do 2 (iRename select (£1) into "Hlc4").
  iMod (start_select_nb_only ch with "[$HisChan] [$Hownchan]") as (γnb) "#Hnb".
  wp_apply (wp_fork with "[Hnb]").
  {
  wp_auto_lc 4.
  wp_apply chan.wp_select_nonblocking.
    simpl.
    iSplitL.
  - (* Prove the receive case - will be vacuous *)
    iSplitL.
    +
      iExists γnb. iExists unit. iExists _, _, _.
      iFrame.
      iSplit.
      { (* Show is_channel matches *)
        iNamed "Hnb". iFrame "#". }
      (* Now use our select_nb_only_rcv_au lemma *)
      iRename select (£1) into "Hlc1".
      iApply (select_nb_only_rcv_au with " [$Hnb]").
      {
      iIntros (v).
      iIntros "Hf".
      done.
      }
      iFrame.
    + (* True case *)
      done.
  - (* Prove the default case *)
    wp_auto.
    done.
  }
  {

  wp_apply chan.wp_select_nonblocking.
    simpl.
    iSplitL "Hlc1 Hlc4".
  - (* Prove the receive case - will be vacuous *)
    iSplitL.
    +
      iExists unit. iExists γnb. iExists _, _, _, _.
      iFrame.
      iSplit.
      { (* Show is_channel matches *)
        iNamed "Hnb". iFrame "#". iPureIntro. done.  }
      (* Now use our select_nb_only_rcv_au lemma *)
       iSplit.
      { (* Show is_channel matches *)
        iNamed "Hnb". iFrame "#". }
      iFrame "#".
      iApply (select_nb_only_send_au γnb ch () with " [$Hnb] []").
      {
        iIntros "Hf".
          done.
      }
      iFrame.
    + (* True case *)
      done.
  - (* Prove the default case *)
    wp_auto.
    iApply "HΦ".
    done.
  }
Qed.

End select_panic.

Section higher_order_example.
Context `{!chan_protocolG Σ request.t}.
Context `{!chan_protocolG Σ go_string}.

Definition do_request (r: request.t) γfut (Q: go_string → iProp Σ) : iProp Σ :=
  "Hf" ∷ WP #r.(request.f') #() {{ λ v, ∃ (s: go_string), ⌜v = #s⌝ ∗ Q s }} ∗
  "#Hfut" ∷ is_future γfut r.(request.result') Q ∗
  "Hfut_tok" ∷ fulfill_token γfut.

Definition await_request (r: request.t) γfut (Q: go_string → iProp Σ) : iProp Σ :=
  "#Hfut" ∷ is_future γfut r.(request.result') Q ∗
  "Hfut_await" ∷ await_token γfut.

Lemma wp_mkRequest {f: func.t} (Q: go_string → iProp Σ) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ WP #f #() {{ λ v, ∃ (s: go_string), ⌜v = #s⌝ ∗ Q s }} }}}
    @! chan_spec_raw_examples.mkRequest #f
  {{{ γfut (r: request.t), RET #r; do_request r γfut Q ∗ await_request r γfut Q }}}.
Proof.
  wp_start as "Hf".
  wp_auto.
  wp_apply chan.wp_make.
  { word. }
  iIntros (ch γ) "(His & _Hcap & Hown)".
  simpl. (* for decide *)
  iMod (start_future with "His Hown") as (γfuture) "(#Hfut & Hawait & Hfulfill)".
  wp_auto.
  iApply "HΦ".
  iFrame "Hfut ∗".
Qed.

#[local] Lemma wp_get_response (r: request.t) γfut Q :
  {{{ await_request r γfut Q }}}
    chan.receive #stringT #r.(request.result')
  {{{ (s: go_string), RET (#s, #true); Q s }}}.
Proof.
  wp_start as "Hawait". iNamed "Hawait".
  wp_apply (wp_future_await with "[$Hfut $Hfut_await]").
  iIntros (v) "HQ".
  iApply "HΦ". done.
Qed.

Definition is_request_chan γ (ch: loc): iProp Σ :=
  is_simple (V:=request.t) γ ch (λ r, ∃ γfut Q, do_request r γfut Q)%I.

Lemma wp_ho_worker γ ch :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_request_chan γ ch }}}
    @! chan_spec_raw_examples.ho_worker #ch
  {{{ RET #(); True }}}.
Proof.
  wp_start as "#His".
  rewrite /is_request_chan.
  wp_auto.
  rewrite /chan.for_range.
  iPersist "c".
  wp_auto.
  iAssert (∃ (r0: request.t),
      "r" ∷ r_ptr ↦ r0
    )%I with "[$r]" as "IH".
  wp_for "IH".
  wp_apply (wp_simple_receive (V:=request.t) with "[$His]") as "%r Hreq".
  iNamed "Hreq".
  wp_bind (#r.(request.f') _)%E.
  iApply (wp_wand with "[Hf]").
  { iApply "Hf". }
  iIntros (v) "HQ".
  iDestruct "HQ" as (s) "[-> HQ]".
  wp_auto.
  wp_apply (wp_future_fulfill with "[$Hfut $Hfut_tok HQ]").
  { done. }
  wp_for_post.
  iFrame.
Qed.

Lemma wp_HigherOrderExample :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.HigherOrderExample #()
  {{{ (s:slice.t), RET #s; s ↦* ["hello world"%go; "HELLO"%go; "world"%go] }}}.
Proof using chan_protocolG0 chan_protocolG1.
  wp_start.
  (* TODO: why is the string unfolded here? *)
  wp_auto.
  wp_apply (chan.wp_make (V:=request.t)).
  { done. }
  iIntros (req_ch γ) "(His & _Hcap & Hown)".
  simpl.
  iMod (start_simple with "His Hown") as "[%γdone #Hch]".
  iAssert (is_request_chan γdone req_ch) with "[$Hch]" as "#Hreqs".
  wp_auto.
  wp_apply (wp_fork).
  {
    wp_apply (wp_ho_worker).
    { iFrame "#". }
    done.
  }
  wp_apply (wp_fork).
  {
    wp_apply (wp_ho_worker).
    { iFrame "#". }
    done.
  }
  wp_apply (wp_mkRequest (λ s, ⌜s = "hello world"%go⌝)%I) as "%γfut1 %r1 [Hdo_r1 Hawait_r1]".
  {
    wp_auto.
    eauto.
  }
  wp_apply (wp_mkRequest (λ s, ⌜s = "HELLO"%go⌝)%I) as "%γfut2 %r2 [Hdo_r2 Hawait_r2]".
  {
    wp_auto.
    eauto.
  }
  wp_apply (wp_mkRequest (λ s, ⌜s = "world"%go⌝)%I) as "%γfut3 %r3 [Hdo_r3 Hawait_r3]".
  {
    wp_auto.
    eauto.
  }
  wp_apply (wp_simple_send (V:=request.t) with "[$Hch $Hdo_r1]").
  wp_apply (wp_simple_send (V:=request.t) with "[$Hch $Hdo_r2]").
  wp_apply (wp_simple_send (V:=request.t) with "[$Hch $Hdo_r3]").
  wp_apply (wp_get_response with "[$Hawait_r1]") as "%s %Heq".
  subst.
  wp_apply (wp_get_response with "[$Hawait_r2]") as "%s %Heq".
  subst.
  wp_apply (wp_get_response with "[$Hawait_r3]") as "%s %Heq".
  subst.
  wp_apply wp_slice_literal.
  iIntros (sl) "Hresponse".
  wp_auto.
  iApply "HΦ".
  done.
Qed.

End higher_order_example.

Section join.
Context `{!chan_protocolG Σ unit}.

Lemma wp_simple_join :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_pkg_init channel    }}}
    @! chan_spec_raw_examples.simple_join #()
  {{{  RET #("Hello, World!"); True }}}.
Proof using chan_protocolG0.
  wp_start. wp_auto_lc 3.
      iRename select (£1) into "Hlc".
  wp_apply chan.wp_make; first done.
  iIntros (ch). iIntros (γ). iIntros "(#HisChan & _Hcap & Hownchan)".
  wp_auto.
  rewrite -fupd_wp.
  simpl.
  iMod (join.own_join_alloc_buff ch γ 1 with "HisChan Hownchan") as (γjoin) "[#Hisjoin Hjoin]".
  iMod ((join.join_alloc_worker γjoin ch
           emp%I ( message_ptr ↦ "Hello, World!"%go) 0)%I with "[$][$Hisjoin] [$Hjoin]")
    as "[Hjoin Hworker]".
  iModIntro. iPersist "ch".
  wp_apply (wp_fork with "[Hworker message]").
  {
    wp_auto.
    wp_apply (join.wp_worker_send with "[$Hisjoin $Hworker $message]").
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
Proof using chan_protocolG0.
  wp_start. wp_auto_lc 3.
  iRename select (£1) into "Hlc1".
  wp_apply chan.wp_make; first done.
  iIntros (ch γ) "(#HisChan & _Hcap & Hownchan)".
  wp_auto.
  rewrite -fupd_wp.
  simpl.
  iMod (join.own_join_alloc_buff ch γ 2 with "HisChan Hownchan") as (γjoin) "[#Hisjoin Hjoin]".
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
    wp_apply (join.wp_worker_send with "[$Hisjoin $Hworker1 $hello]").
    { iFrame. }
  }
  wp_apply (wp_fork with "[Hworker2 world]").
  {
    wp_auto.
    wp_apply (join.wp_worker_send with "[$Hisjoin $Hworker2 $world]").
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

Section muxer.
Context `{!chan_protocolG Σ stream.t}.
Context `{!chan_protocolG Σ go_string}.
Context `{!contributionG Σ (gmultisetUR stream.t)}.
Context `{!dspG Σ go_string}.
(* perennial ghost_var, not iris *)
Context `{!ghost_var.ghost_varG Σ bool}.

Definition mapper_service_prot_aux (Φpre : go_string → iProp Σ) (Φpost : go_string → go_string → iProp Σ)
  (rec : iProto Σ _) : iProto Σ _ :=
  <! (req:go_string)> MSG req {{ Φpre req }} ;
  <? (res:go_string)> MSG res {{ Φpost req res }}; rec.

Instance mapper_service_prot_contractive Φpre Φpost : Contractive (mapper_service_prot_aux Φpre Φpost).
Proof. solve_proto_contractive. Qed.
Definition mapper_service_prot Φpre Φpost := fixpoint (mapper_service_prot_aux Φpre Φpost).
Instance mapper_service_prot_unfold Φpre Φpost :
  ProtoUnfold (mapper_service_prot Φpre Φpost)
    (mapper_service_prot_aux Φpre Φpost (mapper_service_prot Φpre Φpost)).
Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.

Definition is_mapper_stream stream : iProp Σ :=
  ∃ req_ch res_ch f (Φpre : go_string → iProp Σ) (Φpost : go_string → go_string → iProp Σ),
  ⌜stream = {| stream.req' := req_ch; stream.res' := res_ch; stream.f' := f |}⌝ ∗
  "Hf_spec" ∷ □ (∀ (s: go_string),
      Φpre s → WP #f #s {{ λ v, ∃ (s': go_string), ⌜v = #s'⌝ ∗ Φpost s s' }}) ∗
    # (res_ch, req_ch) ↣ iProto_dual (mapper_service_prot Φpre Φpost).

Lemma wp_mkStream (f: func.t) Φpre Φpost :
  {{{ is_pkg_init chan_spec_raw_examples ∗
      "#Hf_spec" ∷ □ (∀ (strng: go_string),
                        Φpre strng -∗ WP #f #strng {{ λ v, ∃ (s': go_string), ⌜v = #s'⌝ ∗ Φpost strng s' }}) }}}
    @! chan_spec_raw_examples.mkStream #f
  {{{ stream, RET #stream;
      is_mapper_stream stream ∗
    # (stream.(stream.req'), stream.(stream.res')) ↣ mapper_service_prot Φpre Φpost }}}.
Proof.
  wp_start. wp_auto.
      wp_apply (chan.wp_make (V:=go_string)); first done.
  iIntros (ch). iIntros (γ). iIntros "(#HisChan & _ & Hownchan)".
  wp_auto_lc 1.
      wp_apply (chan.wp_make (V:=go_string)); first done.
  iIntros (ch1). iIntros (γ1). iIntros "(#HisChan1 & _ & Hownchan1)".
  wp_apply wp_fupd.

  iMod (dsp_session_init _ ch1 ch _ _ _ _
          (mapper_service_prot Φpre Φpost) with "HisChan1 HisChan Hownchan1
 Hownchan")
                       as "[Hpl Hpr]";
    [by eauto|by eauto|..].
  iModIntro. wp_auto.
  iApply "HΦ".
  rewrite /is_mapper_stream.
  iSplitR "Hpl".
  { iExists _, _, _, _, _. iSplit; [done|].
    iDestruct "Hpre" as "#Hpre". iFrame "Hpr".
    iIntros "!>" (s) "HΦ". by iApply "Hpre". }
  iFrame "Hpl".
Qed.

Lemma wp_MapServer (my_stream: stream.t) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_mapper_stream my_stream }}}
    @! chan_spec_raw_examples.MapServer #my_stream
  {{{ RET #(); True }}}.
Proof using chan_protocolG0 chan_protocolG1 globalsGS0.
  wp_start.
  iNamed "Hpre".
  rewrite /chan.for_range.
  wp_auto.
  iDestruct "Hpre" as (Heq) "[#Hf_spec Hprot]".
  iAssert (∃ (in_val: go_string),
    "in" ∷ in_ptr ↦ in_val ∗
    "s" ∷ s_ptr ↦ my_stream ∗

    "Hprot" ∷ # (my_stream.(stream.res'), my_stream.(stream.req')) ↣
                 iProto_dual (mapper_service_prot Φpre Φpost)
  )%I with "[in s Hf_spec Hprot]" as "IH".
  { iExists _. iFrame. subst. iFrame. }

  wp_for.
  iNamed "IH".

  wp_recv (req_val) as "Hreq".
  wp_auto.
  wp_pures.

  wp_bind (#my_stream.(stream.f') #req_val)%E.
  iApply (wp_wand with "[Hf_spec Hreq]").
  { iSpecialize ("Hf_spec" $! req_val). subst. iApply ("Hf_spec" with "Hreq"). }
  iIntros (v) "Hv".
  iDestruct "Hv" as (s') "[%Heq_v Heq_log]".
  subst.
  wp_auto.
  wp_pures.
  wp_send with "[Heq_log]";first done.
  wp_auto.
  wp_for_post.
  iFrame.
Qed.

Lemma wp_Muxer (c: loc) γmpmc (n_prod n_cons: nat) :
  {{{ is_pkg_init chan_spec_raw_examples ∗
      "#Hismpmc" ∷ is_mpmc γmpmc c n_prod n_cons is_mapper_stream (λ _, True) ∗
      "Hcons" ∷ mpmc_consumer γmpmc (∅ : gmultiset stream.t) }}}
    @! chan_spec_raw_examples.Muxer #c
  {{{ RET #(); True%I }}}.
Proof using chan_protocolG0 chan_protocolG1 globalsGS0.
   wp_start. wp_auto_lc 3. iNamed "Hpre".
    rewrite /chan.for_range.
  wp_auto_lc 3.
      iAssert (∃ (received: gmultiset stream.t) (s_val: stream.t),
    "s" ∷ s_ptr ↦ s_val ∗
    "Hcons" ∷ mpmc_consumer γmpmc received
  )%I with "[s Hcons]" as "IH".
  { iExists ∅, _. iFrame. }

  wp_for "IH".
    wp_apply (wp_mpmc_receive with "[$Hcons]").
    {
      iFrame "#".

    }
    iIntros (v).
    iIntros (ok).
    destruct ok.
    {
      iIntros "H". iDestruct "H" as "[Hdat Hcons]".
      iNamed "Hdat".
      wp_auto.
      wp_apply (wp_fork with "[Hdat]").
      {
        by wp_apply (wp_MapServer with "[$Hdat]").
      }
      wp_for_post.
      iFrame.
    }
    {
      iIntros "[#Hclosed Hcons]".
      wp_auto.
      wp_for_post.
      iApply "HΦ".
      done.
    }
Qed.

Lemma wp_makeGreeting :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.makeGreeting #()
  {{{ RET #"Hello, World!"; True%I }}}.
Proof using chan_protocolG0 chan_protocolG1 contributionG0 H dspG0 globalsGS0.
  wp_start. wp_auto.
  wp_apply (chan.wp_make (V:=stream.t) 2); [done|].
  iIntros (c γ) "(#Hic & _ & Hoc)". wp_auto.
  iMod (start_mpmc _ _ _ _ 1 1 with "Hic Hoc") as (γmpmc) "[#Hmpmc [[Hprod _] [Hcons _]]]";
    [done|lia..|].
  wp_apply (wp_fork with "[Hcons]").
  { wp_apply (wp_Muxer with "[Hcons]"); [|done]. iFrame "Hmpmc Hcons". }
  wp_apply (wp_mkStream _ (λ _, True)%I (λ s1 s2, ⌜s2 = s1 ++ ","%go⌝)%I).
  { iIntros (s) "!> _". wp_auto. by eauto. }
  iIntros (stream1) "[Hstream1 Hc1]".
  wp_auto.
  wp_apply (wp_mkStream _ (λ _, True)%I (λ s1 s2, ⌜s2 = s1 ++ "!"%go⌝)%I).
  { iIntros (s) "!> _". wp_auto. by eauto. }
  iIntros (stream2) "[Hstream2 Hc2]".
  wp_auto.
  wp_apply (wp_mpmc_send with "[$Hmpmc $Hprod $Hstream1]").
  iIntros "Hprod".
  wp_auto.
  wp_apply (wp_mpmc_send with "[$Hmpmc $Hprod $Hstream2]").
  iIntros "Hprod".
  wp_auto.
  (* TODO: Proofmode unification fails to find the correct channel *)
  iRevert "Hc2 Hc1". iIntros "Hc2 Hc1".
  wp_send with "[//]".
  wp_auto.
  iRevert "Hc1 Hc2". iIntros "Hc2 Hc1".
  wp_send with "[//]".
  wp_auto.
  iRevert "Hc1 Hc2". iIntros "Hc2 Hc1".
  wp_recv (?) as "->". wp_auto.
  iRevert "Hc1 Hc2". iIntros "Hc1 Hc2".
  wp_recv (?) as "->".
  wp_auto.
  by iApply "HΦ".
Qed.

End muxer.

End proof.
