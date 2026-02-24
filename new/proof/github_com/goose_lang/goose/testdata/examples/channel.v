From New.proof Require Export proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel
Require Import idiom.base handoff future spsc done dsp dsp_proofmode mpmc join handshake.
From New.proof Require Import strings time sync.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.
From iris.base_logic Require Import ghost_map.
From New.golang Require Import theory.
From New.proof Require Import strings.
From iris.algebra Require Import gmultiset.

Import New.code.github_com.goose_lang.goose.testdata.examples.channel.chan_spec_raw_examples.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : chan_spec_raw_examples.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) chan_spec_raw_examples := build_get_is_pkg_init_wf.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Instance func_countable : Countable func.t.
Proof. Admitted.

Instance stream_eq_dec : EqDecision chan_spec_raw_examples.streamold.t.
Proof. solve_decision. Qed.
Instance stream_countable : Countable chan_spec_raw_examples.streamold.t.
Proof.
  refine (inj_countable'
           (λ x, (streamold.req' x, streamold.res' x, streamold.f' x))
          (λ '(a, b, c), streamold.mk a b c) _).
  by intros [].
Defined.

Section select_full_buffer.

(* Invariant for the “full buffer” situation                                  *)

(** Invariant: channel must be Buffered [W64 0] (full for cap = 1). *)
Definition is_select_nb_full1 (γ : chan_names) (ch : loc) : iProp Σ :=
  "#Hch"  ∷ is_chan ch γ w64 ∗
  "%Hcap1" ∷ ⌜chan_cap γ = (W64 1)⌝ ∗
  "#Hinv" ∷ (own_chan γ w64 (chanstate.Buffered [W64 0])).

Lemma start_select_nb_full1 (ch : loc) (γ : chan_names) :
  is_chan ch γ w64 -∗
  ⌜chan_cap γ = (W64 1)⌝ -∗
  own_chan γ w64 (chanstate.Buffered [W64 0]) ={⊤}=∗
  is_select_nb_full1 γ ch.
Proof.
  iIntros "#Hch %Hcap Hoc".
  iModIntro. iFrame "#". iFrame "%". iFrame.
Qed.

Lemma select_nb_full1_send_au (γ : chan_names) (ch : loc) :
  ∀ Φ Φnotready,
    is_select_nb_full1 γ ch -∗
    Φnotready -∗
    nonblocking_send_au γ (W64 0) Φ Φnotready.
Proof.
  intros Φ Φnotready.
  iIntros "Hfull Hnotready".
  iNamed "Hfull".
  iSplit; last done.
  iApply fupd_mask_intro; [solve_ndisj|].
  iIntros "Hmask". iNext.

  iExists (chanstate.Buffered [W64 0]).
  iFrame.
  iIntros "Hoc'".
  (* Show this contradicts the capacity bound. *)
  iPoseProof (own_chan_buffer_size with "Hoc'") as "%Hle".
  rewrite Hcap1 in Hle.
  done.
Qed.

Lemma SendAU_from_empty_buffer_to
    (ch: loc) (γ: chan_names) (Φ : iProp Σ) :
  own_chan γ w64 (chanstate.Buffered []) -∗
  (own_chan γ w64 (chanstate.Buffered [W64 0]) -∗ Φ) -∗
  send_au γ (W64 0) Φ.
Proof.
  iIntros "Hoc Hk".
  unfold send_au.
  iApply fupd_mask_intro; [solve_ndisj|].
  iIntros "Hmask". iNext.
  iExists (chanstate.Buffered []).
  iFrame "Hoc".
  simpl.
  iIntros "Hoc'".
  iMod "Hmask".
  iApply ("Hk" with "Hoc'").
Qed.

(* 
  From a send on full buffer (which blocks indefinitely), any Φ can be derived 
*)
Lemma SendAU_full_cap1_vacuous
  (ch : loc) (γ : chan_names) (v0 v : w64) (Φ : iProp Σ) :
  chan_cap γ = (W64 1) ->
  own_chan γ w64 (chanstate.Buffered [v0]) -∗
  send_au γ v Φ.
Proof.
  intros Hcap.
  iIntros "Hoc".
  unfold send_au.
  iApply fupd_mask_intro; [solve_ndisj|].
  iIntros "Hmask". iNext.
  iExists (chanstate.Buffered [v0]).
  iFrame "Hoc".
  simpl.
  iIntros "Hoc'".
  iPoseProof (own_chan_buffer_size with "Hoc'") as "%Hle".
  rewrite Hcap in Hle.
  done.
Qed.

Lemma wp_select_nb_full_buffer_no_panic :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.select_nb_full_buffer_no_panic #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto_lc 2.

  wp_apply (chan.wp_make2); first done.
  iIntros (ch γ) "(#His_chan & %Hcap & Hown)".
  wp_auto.

  (* First send: use the empty-buffer AU to fill buffer to [0]. *)
  wp_apply (chan.wp_send ch (W64 0) γ with "[$His_chan]").
  iIntros "Hlc_send". simpl.
  iApply ((SendAU_from_empty_buffer_to ch γ) with "Hown").

  (* Now we have: own_chan ch (Buffered [0]) γ in the continuation. *)
  iIntros "Hoc".
  iMod (start_select_nb_full1 ch γ with "[$His_chan] [%] [$Hoc]") as "Hfull".
{ exact Hcap. }  (* supplies ⌜chan_cap γ = 1⌝ *)
wp_auto.

  (* Nonblocking select: show send case is disabled -> default taken. *)
  wp_apply chan.wp_select_nonblocking.

  iSplit.
  - simpl. iSplit; last done.
    iExists w64, ch,γ, (W64 0). repeat iExists _.
    
    iSplit; [iPureIntro; split;first done;reflexivity|].
    iSplit; [iFrame "#"; done|].
    (* AU for send case: forced not-ready by full-buffer invariant. 
      => We can get contradiction
    *)
    iApply (select_nb_full1_send_au γ ch with "[$Hfull]"). 
    all:try done.
  - (* default branch *)
    wp_auto. iApply "HΦ". done.
    Unshelve.
    + apply sem.
    + apply _.
Qed.

(* Example 2: buffer space -> panic branch ready -> fails to verify  *)

Lemma wp_select_nb_buffer_space_panic_fails :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.select_nb_buffer_space_panic #()
  {{{ RET #(); True }}}.
  Proof.
  wp_start. wp_auto_lc 2.
  wp_apply (chan.wp_make2); first done.
  iIntros (ch γ) "(#His_chan & %Hcap & Hown)".

  wp_auto.
  wp_apply chan.wp_select_nonblocking.
  simpl.

  (* Split (case package) and default. *)
  iSplit.
  - iSplit; last done.
    iExists w64, ch, γ, _, _, _,_.
    iSplit; [iPureIntro; first done;reflexivity|].
    iSplit; [iFrame "#"; done|].
    unfold nonblocking_send_au.
    iSplit; last done.
    iApply fupd_mask_intro; [solve_ndisj|].
    iIntros "Hmask". iNext.
    iExists (chanstate.Buffered []).
    iFrame "Hown".
    simpl.
    iIntros "Hoc".
    iMod "Hmask".
    iModIntro. wp_auto.  
    (* Branch fails here *)
    admit.
  - wp_auto. iApply "HΦ". done.
Abort.

(* Example 3: deadlock on blocking select send -> vacuously verifies  *)
Lemma wp_select_nb_buffer_space_deadlock_vacuous :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.select_nb_buffer_space_deadlock #()
  {{{ RET #(); True }}}.
  Proof.
  wp_start. wp_auto.
  wp_apply (chan.wp_make2); first done.
  iIntros (ch γ) "(#His_chan & %Hcap & Hown)".
  wp_auto.
  wp_apply (chan.wp_send ch (W64 0) γ with "[$His_chan]").

  (* First send: fill the buffer. We verify it by giving a SendAU that
     updates Buffered [] -> Buffered [0], then continues. *)
  iIntros "Hlc". simpl.
 
  iApply ((SendAU_from_empty_buffer_to (ch) (γ) 
         ) with "Hown").
      
         iIntros "Hoc". wp_auto.
  wp_apply chan.wp_select_blocking.
  simpl.
  iSplitL "Hoc".
  - iExists w64,ch, γ, (W64 0), _, _, _. 
    iSplit.
    { iPureIntro. split;first done;done. }
    iSplitL "".
    { iFrame "#". }

  iApply (SendAU_full_cap1_vacuous (ch) (γ)
              (W64 0) (W64 0)).
              { done. }
              
              done.
              - done.
              Unshelve.
              { apply sem.  }
              { apply _. }
Qed.

End select_full_buffer.

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
  {{{ (ch: loc)  (γfut: handoff_names), RET #ch;
       is_chan ch γfut.(handoff.chan_name) go_string ∗
  is_chan_handoff (V:=go_string) γfut ch (λ (v : go_string), ⌜v = "Hello, World!"%go⌝)
    }}}.
Proof.
  wp_start. wp_auto.
  wp_apply chan.wp_make2; first done.
  iIntros (ch). iIntros (γ). iIntros "(#His_chan & Hcap & Hownchan)".
  wp_auto.
  simpl in *.
  iMod ((start_handoff_buffered ch γ (λ (v : go_string), ⌜v = "Hello, World!"%go⌝)%I)
         with "His_chan Hownchan") as "(%γdone & %Hd & #Hch)".
  iPersist "ch".
  wp_apply (wp_fork).
  {
    wp_auto.
    wp_apply wp_sys_hello_world.
    iAssert (⌜"Hello, World!"%go = "Hello, World!"%go⌝)%I as "HP".
    { iPureIntro. reflexivity. }
  wp_apply (wp_handoff_send (V:=go_string) with "[$Hch]").
    { done. }
    done.
    }
  iApply "HΦ".
  subst γ.
  iFrame "∗#".
Qed.

Lemma wp_HelloWorldSync :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.HelloWorldSync #()
  {{{ RET #("Hello, World!"); True }}}.
Proof.
  wp_start.
  wp_apply wp_HelloWorldAsync.
  iIntros (ch γfuture) "[#Hchan #Hfut]".
  wp_apply (wp_handoff_receive with "Hfut").
  iIntros (v) "%Hv".
  wp_auto.
  subst v.
  iApply "HΦ".
  done.
Qed.

End hello_world.


Section cancellable.


Lemma wp_HelloWorldCancellable
  (done_ch : loc) (err_ptr1: loc) (err_msg: go_string)
  (γdone: done_names) :
  {{{ is_pkg_init chan_spec_raw_examples ∗
        is_done (V:=unit)  γdone done_ch ∗
        Notified γdone (err_ptr1 ↦ err_msg)  }}}
    @! chan_spec_raw_examples.HelloWorldCancellable #done_ch #err_ptr1
    {{{
(result: go_string), RET #result;
      ⌜result = err_msg ∨ result = "Hello, World!"%go⌝
    }}}.
Proof.
  wp_start. wp_apply wp_alloc.
  iIntros (l). iIntros "Herr".
  wp_auto_lc 4.
  do 2 (iRename select (£1) into "Hlc2").
  wp_apply wp_HelloWorldAsync.
  iIntros (ch γfuture) "[#Hch #Hfut]". wp_auto_lc 1.
  do 2 (iRename select (£1) into "Hlc1").
  iDestruct "Hpre" as "(#H1 & H2)".
 
  iFrame "#".
  wp_apply chan.wp_select_blocking.
  simpl.
    iSplit.
    {
      repeat iExists _; iSplitR; first done. iFrame "#".

      iApply (handoff_rcv_au (V:=go_string)  γfuture ch with "[$Hfut] [$]").
      iNext. iIntros (v). iIntros "%Hw".
      wp_auto.
      subst v.
      iApply "HΦ".
      iPureIntro.
      right. done.
    }
    {
      iSplitL; last done. repeat iExists _; iSplitR; first done. iFrame "#".
      iSplitL "". { iApply (done_is_chan γdone done_ch (V:=unit) (t:=(go.StructType []))).  iFrame "#". }
      iApply ((done_receive_au (V:=unit) (t:=((go.StructType []))) γdone done_ch) with "[$H1] [$H2] [HΦ Herr] [$]").
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
Proof.
  wp_start.
  wp_auto. wp_apply chan.wp_make1.
  iIntros (ch γ) "(#Hchan & _Hcap & Hoc)".
  simpl.
  iDestruct (start_done (t:=(go.StructType [])) ch γ with "Hchan") as "Hstart".
  iMod ("Hstart" with "Hoc") as (γdone) "(#Hdone & Hnot)".
  wp_auto.
  iPersist "done".

  iMod (done_alloc_notified (t:=(go.StructType []))  _ _ _ (errMsg_ptr ↦ "operation timed out"%go)%I
         with "[$Hdone] [$Hnot]") as "[HNotify HNotified]".
  wp_apply (wp_fork with "[HNotify errMsg done]").
  { wp_auto.
    wp_apply wp_Sleep.
    wp_apply (chan.wp_close with "[]") as "(Hlc1 & Hlc2 & Hlc3 & _)".
    { iApply (done_is_chan (t:=(go.StructType [])) with "Hdone"). }
    iApply (done_close_au (t:=(go.StructType [])) with "[$] [$] [$HNotify errMsg]").
    { iFrame. }
    iNext.
    wp_auto.
    done. }

  wp_apply (wp_HelloWorldCancellable with "[$Hdone $HNotified] [HΦ]").
  {
    iFrame "#".
    iIntros (result).
    iIntros "%Hres".
    wp_auto.
    iApply "HΦ".
    iPureIntro. destruct Hres; auto. }
Qed.

End cancellable.


Section fibonacci_examples.

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
      spsc_producer γ ([] : list w64)
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

    wp_apply (wp_spsc_send with "[Hspsc Hprod]").
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
        { word. }
      }
      { word. }
    }
    { rewrite !fib_succ. word. }
  }
  {
    wp_apply (wp_spsc_close with "[$Hspsc $Hprod]").
    { iFrame "#".   iPureIntro. rewrite Hsl.
      assert ((length sent) = sint.nat n).
      {
        assert (length sent < 2^64). { lia. }
        word.
      }
      destruct (length sent) eqn: H1.
      { word. }
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
Proof.
  wp_start. wp_auto.
  wp_apply chan.wp_make2; first done.
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
      replace (sint.nat (γ.(chan_cap))) with 10%nat by word.
      iFrame "#".
    }
    done.
  }
  simpl.
  wp_apply wp_slice_literal as "% _".
  { iIntros. wp_auto. iFrame. }
  iAssert (∃ (i: nat) (i_v: w64) sl,
              "i" ∷ i_ptr ↦ i_v ∗
              "Hcons"  ∷ spsc_consumer γspsc (fib_list i) ∗
              "Hsl"  ∷ sl ↦* (fib_list i) ∗
              "results"  ∷ results_ptr ↦ sl ∗
              "oslc"  ∷ theory.slice.own_slice_cap w64 sl (DfracOwn 1)
          )%I
    with "[ i Hcons results]" as "IH".
  {
    iExists 0%nat.
    iFrame.
    unfold fib_list. iFrame "#".
    iDestruct own_slice_empty as "$"; [done..|].
    iDestruct own_slice_cap_empty as "$"; done.
  }

  wp_for "IH".
   wp_apply (wp_spsc_receive with "[Hcons]").
   { iFrame "#".  iFrame.   }
   iIntros (v ok).
   destruct ok.
   {
     iIntros "[%Hfib Hcons]".


      wp_auto.
      iDestruct (slice.own_slice_len with "Hsl") as "[%Hl %Hcap]".
      iDestruct (slice.own_slice_len with "Hsl") as "[%Hlen_slice %Hslgtz]".


wp_apply wp_slice_literal. { iIntros. wp_auto. iFrame. } iIntros (sl0) "[Hsl0 _]".
      iDestruct (slice.own_slice_len with "Hsl0") as "[%Hl0 %Hcap0]".
      iDestruct (slice.own_slice_len with "Hsl0") as "[%Hlen_slice0 %Hslgtz0]".
wp_auto.
wp_apply (wp_slice_append with "[$Hsl $Hsl0 $oslc ]").

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
   destruct Hfl as [H1 H2].
   rewrite H1.
   iFrame "Hsl".
Qed.

End fibonacci_examples.

Section dsp_examples.
Context `{!dspG Σ interface.t}.

Definition ref_prot : iProto Σ interface.t :=
  <! (l:loc) (x:Z)> MSG (interface.mk_ok (go.PointerType go.int) #l) {{ l ↦ W64 x }} ;
  <?> MSG (interface.mk_ok (go.StructType []) #()) {{ l ↦ w64_word_instance.(word.add) (W64 x) (W64 2) }} ;
  END.
Lemma wp_DSPExample :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.DSPExample #()
  {{{ RET #(W64 42); True }}}.
Proof using dspG0 W.
  wp_start. wp_auto.
  wp_apply chan.wp_make1.
  iIntros (c γ) "(#Hic & _Hcap & Hoc)". wp_auto.
  wp_apply chan.wp_make1.
  iIntros (signal γ') "(#Hicsignal & _Hcapsignal & Hocsignal)". wp_auto.
  iMod (dsp_session_init _ _ _ _ _ _ _ ref_prot with "Hic Hicsignal Hoc Hocsignal")
                       as (γdsp1 γdsp2) "[Hc Hcsignal]";
    [by eauto|by eauto|..].
  iPersist "c signal".
  wp_apply (wp_fork with "[Hcsignal]").
  { wp_auto.
    wp_recv (l x) as "Hl".
    wp_auto. rewrite -> decide_True; last done. wp_auto.
    wp_send with "[$Hl]".
    by wp_auto. }
  wp_send with "[$val]".
  wp_auto.
  wp_recv as "Hl".
  wp_auto. by iApply "HΦ".
Qed.

End dsp_examples.

Section select_panic.

(** Invariant: channel must be Idle, all other states are False *)
Definition is_select_nb_only (γ : chan_names) (ch : loc) : iProp Σ :=
  "#Hch" ∷ is_chan ch γ unit ∗
  "#Hinv" ∷ inv nroot (
      ∃ s,
        "Hoc" ∷ own_chan γ unit s ∗
        "%" ∷ ⌜ (match s with
                | chanstate.Idle => True
                | _ => False
                end) ⌝
  ).


(** Create the idiom from a channel in Idle state *)
Lemma start_select_nb_only (ch : loc) (γ : chan_names) :
  is_chan ch γ unit -∗
  own_chan γ unit chanstate.Idle ={⊤}=∗
  is_select_nb_only γ ch.
Proof.
  iIntros "#Hch Hoc".
  iMod (inv_alloc nroot with "[Hoc]") as "$".
  { iNext. iFrame. }
  simpl.
  by iFrame "#".
Qed.

(** Nonblocking send AU - vacuous since we ban all send preconditions *)
Lemma select_nb_only_send_au γ ch (v : unit) :
  ∀ Φ Φnotready,
  is_select_nb_only γ ch -∗
  ( False -∗  Φ) -∗
  Φnotready -∗
  nonblocking_send_au γ v Φ Φnotready.
Proof.
   intros Φ Φnotready.
  iIntros "#Hnb _ Hnotready".
  iNamed "Hnb".
  iSplit.
   - iInv "Hinv" as ">Hinv_open" "Hinv_close".
     iNamed "Hinv_open".
     destruct s; try done.
     (* Only Idle case remains - all others give False from invariant *)
     iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
     iNext.
     iFrame.
   - done.
Qed.


(** Nonblocking receive AU - vacuous since we ban all receive preconditions *)
Lemma select_nb_only_rcv_au γ ch :
   ∀ (Φ: unit → bool → iProp Σ) (Φnotready: iProp Σ),
  is_select_nb_only γ ch -∗
  (∀ (v:unit), False -∗ Φ v true) -∗
  Φnotready -∗
  nonblocking_recv_au γ unit (λ (v:unit) (ok:bool), Φ v ok) Φnotready.
Proof.
  intros Φ Φnotready.
  iIntros "#Hnb _ Hnotready".
  iNamed "Hnb".
  iSplit.
  - iInv "Hinv" as ">Hinv_open" "Hinv_close".
    iNamed "Hinv_open".
    destruct s; try done.
    (* Only Idle case remains - all others give False from invariant *)
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext.
    iFrame.
  - done.
Qed.


Lemma wp_select_nb_no_panic :
  {{{ is_pkg_init chan_spec_raw_examples}}}
    @! chan_spec_raw_examples.select_nb_no_panic #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto_lc 2.
  wp_apply chan.wp_make1.
  iIntros (ch). iIntros (γ). iIntros "(#His_chan & _Hcap & Hownchan)".
  iRename select (£1) into "Hlc1".
  wp_auto_lc 2.
  iRename select (£1) into "Hlc2".
  simpl.
  iPersist "ch".
  do 2 (iRename select (£1) into "Hlc4").
  iMod (start_select_nb_only ch with "[$His_chan] [$Hownchan]") as "#Hnb".
  wp_apply (wp_fork with "[Hnb]").
  {
  wp_auto_lc 4.
  wp_apply chan.wp_select_nonblocking.
    simpl.
    iSplitL.
  - (* Prove the receive case - will be vacuous *)
    iSplitL.
    +
      repeat iExists _; iSplitR; first done.
      (* extract is_chan *)
      iPoseProof "Hnb" as "[$ _]".
      (* Now use our select_nb_only_rcv_au lemma *)
      iRename select (£1) into "Hlc1".
      iApply (select_nb_only_rcv_au with " [$Hnb]").
      {
      iIntros (v).
      iIntros "Hf".
      done.
      }
      done.
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
    iSplitL; last done.
    repeat iExists _; iSplitR; first done. iFrame "#". iClear "His_chan".
    iApply (select_nb_only_send_au with "[$Hnb] []").
    {
      iIntros "Hf".
      done.
    }
    iFrame.
  - (* Prove the default case *)
    wp_auto.
    iApply "HΦ".
    done.
  }
Qed.

End select_panic.

Section higher_order_example.

Context `{!ghost_map.ghost_mapG Σ gname (go_string → iProp Σ)}.
Context `{!inG Σ unitR}.

Definition do_request (r: request.t) γfut (Q: go_string → iProp Σ) : iProp Σ :=
  "Hf" ∷ WP #r.(request.f') #() {{ λ v, ∃ (s: go_string), ⌜v = #s⌝ ∗ Q s }} ∗
  "#Hfut" ∷ is_future (V:=go_string)  γfut r.(request.result') ∗
  "Hpromise" ∷ Fulfill (V:=go_string)  γfut Q.

Definition await_request (r: request.t) γfut (Q: go_string → iProp Σ) : iProp Σ :=
  "#Hfut" ∷ is_future (V:=go_string) γfut r.(request.result') ∗
  "HAwait" ∷ Await (V:=go_string) γfut [Q].

Lemma wp_mkRequest {f: func.t} (Q: go_string → iProp Σ) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ WP #f #() {{ λ v, ∃ (s: go_string), ⌜v = #s⌝ ∗ Q s }} }}}
    @! chan_spec_raw_examples.mkRequest #f
  {{{ γfut (r: request.t), RET #r; do_request r γfut Q ∗ await_request r γfut Q }}}.
  Proof using H ext ffi ffi_interp0 ffi_semantics0 hG inG0 package_sem sem Σ.
  wp_start as "Hf".
  wp_auto.
  wp_apply chan.wp_make2; first done.
  iIntros (ch γ) "(His & _Hcap & Hown)".
  simpl.
  iMod (start_future (V:=go_string)  (t:=go.string) (ghost_mapG0:=H)   ch γ (chanstate.Buffered []) with "[$His] [$Hown]") as (γfuture) "(#Hfut & HAwait)".
  { right. done. }
  iMod (future_alloc_promise (V:=go_string) (t:=go.string) γfuture ch Q [] with "Hfut HAwait") as "(Hpromise & HAwait)".
  wp_auto.
  iApply "HΦ".
  iFrame "Hfut Hf Hpromise HAwait".
Qed.

#[local] Lemma wp_get_response r γfut Q :
  {{{ await_request r γfut Q }}}
    chan.receive go.string #r.(chan_spec_raw_examples.request.result')
  {{{ (s: go_string), RET (#s, #true); Q s }}}.
  Proof using H ext ffi ffi_interp0 ffi_semantics0 hG inG0 package_sem sem Σ.

  wp_start as "Hawait". iNamed "Hawait".
  wp_apply (wp_future_await with "[$Hfut $HAwait]").
  iIntros (v P pre post) "(%Hsplit & HP & _HAwait)".
  destruct pre as [|? pre']; simpl in Hsplit.
  - injection Hsplit as <-. 
    destruct post as [|? post']; last done.
    iApply "HΦ". iFrame.
  -  iApply "HΦ". exfalso.
    assert (length [Q] = length (u :: pre' ++ P :: post)) as Hlen by (rewrite Hsplit; done).
    simpl in Hlen.
    rewrite app_length in Hlen.
    simpl in Hlen.
    lia.
Qed.

Definition is_request_chan γ (ch: loc): iProp Σ :=
  is_chan_handoff (V:=chan_spec_raw_examples.request.t) γ ch (λ r, ∃ γfut Q, do_request r γfut Q)%I.

Lemma wp_ho_worker γ ch :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_request_chan γ ch }}}
    @! chan_spec_raw_examples.ho_worker #ch
  {{{ RET #(); True }}}.
  Proof using H ext ffi ffi_interp0 ffi_semantics0 hG inG0 package_sem sem Σ.
  wp_start as "#His".
  rewrite /is_request_chan.
  wp_auto.
  iAssert (∃ (r0: chan_spec_raw_examples.request.t),
      "r" ∷ r_ptr ↦ r0
    )%I with "[$r]" as "IH".
  wp_for "IH".
  wp_apply (wp_handoff_receive with "[$His]") as "%r Hreq".
  iNamed "Hreq".
  wp_bind.
  iApply (wp_wand with "[Hf]").
  { iApply "Hf". }
  iIntros (v) "HQ".
  iDestruct "HQ" as (s) "[-> HQ]".
  wp_auto.
  wp_apply (wp_future_fulfill with "[$Hfut $Hpromise HQ]").
  { done. }
  wp_for_post.
  iFrame.
Qed.

Lemma wp_HigherOrderExample :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.HigherOrderExample #()
  {{{ (s:slice.t), RET #s; s ↦* ["hello world"%go; "HELLO"%go; "world"%go] }}}.
  Proof using H ext ffi ffi_interp0 ffi_semantics0 hG inG0 package_sem sem Σ.
  wp_start.
  wp_auto.
  wp_apply chan.wp_make1.
  iIntros (req_ch γ) "(His & _Hcap & Hown)".
  simpl.
  iMod (start_handoff with "His Hown") as "(%γdone & %Hsimpch & #Hch)".
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
  wp_apply (wp_handoff_send with "[$Hch $Hdo_r1]").
  wp_apply (wp_handoff_send with "[$Hch $Hdo_r2]").
  wp_apply (wp_handoff_send with "[$Hch $Hdo_r3]").
  wp_apply (wp_get_response with "[$Hawait_r1]") as "%s %Heq".
  subst.
  wp_apply (wp_get_response with "[$Hawait_r2]") as "%s %Heq".
  subst.
  wp_apply (wp_get_response with "[$Hawait_r3]") as "%s %Heq".
  subst.
  wp_apply wp_slice_literal.
  { iIntros. wp_auto. iFrame. }
  iIntros (sl) "Hresponse".
  wp_auto.
  iApply "HΦ".
  done.
Qed.

End higher_order_example.

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

Section serve.
Context `{!dspG Σ go_string}.

Definition service_prot_aux (Φpre : go_string → iProp Σ) (Φpost : go_string → go_string → iProp Σ)
  (rec : iProto Σ _) : iProto Σ _ :=
  <! (req:go_string)> MSG req {{ Φpre req }} ;
  <? (res:go_string)> MSG res {{ Φpost req res }}; rec.

Instance service_prot_contractive Φpre Φpost : Contractive (service_prot_aux Φpre Φpost).
Proof. solve_proto_contractive. Qed.

Definition service_prot Φpre Φpost := fixpoint (service_prot_aux Φpre Φpost).

Instance service_prot_unfold Φpre Φpost :
  ProtoUnfold (service_prot Φpre Φpost)
    (service_prot_aux Φpre Φpost (service_prot Φpre Φpost)).
Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.

(* Serve - creates stream, spawns server, returns client endpoint *)
Lemma wp_Serve (f: func.t) Φpre Φpost  :
  {{{ is_pkg_init chan_spec_raw_examples ∗
      "#Hf_spec" ∷ □ (∀ (strng: go_string),
          Φpre strng → WP #f #strng {{ λ v, ∃ (s': go_string), ⌜v = #s'⌝ ∗ Φpost strng s' }}) }}}
    @! chan_spec_raw_examples.Serve #f
  {{{ stream γ , RET #stream;
      (stream.(chan_spec_raw_examples.stream.req'),
          stream.(chan_spec_raw_examples.stream.res'))  ↣{γ} service_prot Φpre Φpost }}}.
Proof.
  wp_start.
  iNamed "Hpre".
  wp_auto.

  wp_apply chan.wp_make1.
  iIntros (res_ch γ_res) "(#Hres & _ & Hown_res)".
  wp_auto_lc 1.

  (* Make req channel *)
  wp_apply chan.wp_make1.
  iIntros (req_ch γ_req) "(#Hreq & _ & Hown_req)".



  (* Initialize idiom *)
  wp_apply wp_fupd.
  iMod (dsp_session_init _ res_ch req_ch _ _ _ _
          (service_prot Φpre Φpost)
        with "Hres Hreq Hown_res Hown_req") as (γdsp1 γdsp2) "[Hclient Hserver]";
    [by eauto|by eauto|..].
  iModIntro.
  wp_auto.
  iPersist "s".

  wp_apply (wp_fork with "[Hserver f]").
  {
    wp_auto.
      iAssert (

    "Hprot" ∷  (req_ch, res_ch)  ↣{γdsp2}
                 iProto_dual (service_prot Φpre Φpost)
  )%I with "[s Hserver]" as "IH".
  { iFrame. }
    wp_for "IH".
  {


  wp_recv (req_val) as "Hre".
  wp_auto.
  wp_bind (#f #req_val)%E.
  iApply (wp_wand with "[Hf_spec Hre]").
  {
     iSpecialize ("Hf_spec" $! req_val). subst. iApply ("Hf_spec" with "Hre").
  }
  iIntros (v).
  iIntros "H".
  iDestruct "H" as (s') "[%Heq_v Heq_log]".
  wp_auto.
  subst.
  wp_send with "[Heq_log]".
  {
    done.
  }
  wp_auto.
  wp_for_post.
  iFrame.
  }
}
iApply "HΦ".
  done.
  Qed.

Lemma wp_appWrld (s: go_string) :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.appWrld #s
  {{{ RET #(s ++ ", World!"%go); True }}}.
Proof.
  wp_start.
  wp_auto.
  by iApply "HΦ".
Qed.

Lemma wp_Client:
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.Client #()
  {{{ RET #"Hello, World!"; True%I }}}.
Proof using dspG0 W.
  wp_start.
  wp_auto.

  wp_apply (wp_Serve _ (λ _, True%I) (λ s1 s2, ⌜s2 = s1 ++ ", World!"%go⌝%I)).
  { iIntros "!>" (s) "_". wp_apply wp_appWrld. iExists  (s ++ ", World!"%go). iPureIntro. done.
    }
  iIntros (hw γ) "Hprot".
  wp_auto.

  wp_send with "[//]".
  wp_auto.

  wp_recv (?) as "->".
  wp_auto.
  by iApply "HΦ".
Qed.

End serve.


Section muxer.
Context `{!contributionG Σ (gmultisetUR streamold.t)}.
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
  ∃ γ req_ch res_ch f (Φpre : go_string → iProp Σ) (Φpost : go_string → go_string → iProp Σ),
  ⌜stream = {| streamold.req' := req_ch; streamold.res' := res_ch; streamold.f' := f |}⌝ ∗
  "Hf_spec" ∷ □ (∀ (s: go_string),
      Φpre s → WP #f #s {{ λ v, ∃ (s': go_string), ⌜v = #s'⌝ ∗ Φpost s s' }}) ∗
    (res_ch, req_ch) ↣{γ} iProto_dual (mapper_service_prot Φpre Φpost).

Lemma wp_mkStream (f: func.t) Φpre Φpost :
  {{{ is_pkg_init chan_spec_raw_examples ∗
      "#Hf_spec" ∷ □ (∀ (strng: go_string),
                        Φpre strng -∗ WP #f #strng {{ λ v, ∃ (s': go_string), ⌜v = #s'⌝ ∗ Φpost strng s' }}) }}}
    @! chan_spec_raw_examples.mkStream #f
  {{{ γ stream, RET #stream;
      is_mapper_stream stream ∗
      (stream.(streamold.req'), stream.(streamold.res')) ↣{γ} mapper_service_prot Φpre Φpost }}}.
Proof.
  wp_start. wp_auto.
  wp_apply chan.wp_make1.
  iIntros (ch1). iIntros (γ1). iIntros "(#His_chan1 & _ & Hownchan1)".
  wp_auto_lc 1. wp_apply chan.wp_make1.
  iIntros (ch). iIntros (γ). iIntros "(#His_chan & _ & Hownchan)".
  wp_apply wp_fupd.

  iMod (dsp_session_init _ ch1 ch _ _ _ _
          (mapper_service_prot Φpre Φpost) with "His_chan1 His_chan Hownchan1 Hownchan")
    as (γdsp1 γdsp2) "[Hpl Hpr]";
    [by eauto|by eauto|..].
  iModIntro. wp_auto.
  iApply "HΦ".
  simpl. iSplitR "Hpl"; [ | iFrame ]. (* iSplit is for performance *)
  rewrite /is_mapper_stream /=.
  iExists _, _, _, _, _, _. iSplit; [done|].
  iDestruct "Hpre" as "#Hpre". iFrame "Hpr".
  iIntros "!>" (s) "HΦ". by iApply "Hpre".
Qed.

Lemma wp_MapServer (my_stream: streamold.t) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_mapper_stream my_stream }}}
    @! chan_spec_raw_examples.MapServer #my_stream
  {{{ RET #(); True }}}.
Proof.
  wp_start.
  iNamed "Hpre".
  wp_auto.
  iDestruct "Hpre" as (Heq) "[#Hf_spec Hprot]".
  iAssert (
    "s" ∷ s_ptr ↦ my_stream ∗

    "Hprot" ∷ (my_stream.(streamold.res'), my_stream.(streamold.req')) ↣{γ}
                 iProto_dual (mapper_service_prot Φpre Φpost)
  )%I with "[s Hf_spec Hprot]" as "IH".
  { iFrame. subst. iFrame. }

  wp_for.
  iNamed "IH".
  wp_auto.

  wp_recv (req_val) as "Hreq".
  wp_auto.
  wp_pures.

  wp_bind (#my_stream.(streamold.f') #req_val)%E.
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

Lemma wp_MapClient (my_stream: streamold.t) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_mapper_stream my_stream }}}
    @! chan_spec_raw_examples.ClientOld #()
  {{{ RET #"Hello, World!"; True%I }}}.
Proof.
  wp_start.
  wp_auto.
    wp_apply (wp_mkStream _ (λ _, True)%I (λ s1 s2, ⌜s2 = s1 ++ ","%go⌝)%I).
    {
       iIntros (s) "!> _". wp_auto. by eauto.
    }
    iIntros (γ stream).
    iIntros "Hmapper".
    wp_auto.
    wp_apply (wp_mkStream _ (λ _, True)%I (λ s1 s2, ⌜s2 = s1 ++ "!"%go⌝)%I).
    {
       iIntros (s) "!> _". wp_auto. by eauto.
    }
    iIntros (γ' s').
    iIntros "H'".
    wp_auto.
    iDestruct "Hmapper" as "[Hmapper Hstr]".
    iDestruct "H'" as "[Hmapper' Hstr']".

  wp_apply (wp_fork with "[Hmapper]").
  {
        wp_apply (wp_MapServer with "[$Hmapper]").
done.
  }
  wp_apply (wp_fork with "[Hmapper']").
  {
        wp_apply (wp_MapServer with "[$Hmapper']").
done.
  }
  wp_send with "[//]".
  wp_auto.
  wp_send with "[//]".
  wp_auto.
  wp_recv (?) as "->". wp_auto.
  wp_recv (?) as "->". wp_auto.
  iApply "HΦ".
  done.
Qed.

Lemma wp_Muxer (c: loc) γmpmc (n_prod n_cons: nat) :
  {{{ is_pkg_init chan_spec_raw_examples ∗
      "#Hismpmc" ∷ is_mpmc γmpmc c n_prod n_cons is_mapper_stream (λ _, True) ∗
      "Hcons" ∷ mpmc_consumer γmpmc (∅ : gmultiset streamold.t) }}}
    @! chan_spec_raw_examples.Muxer #c
  {{{ RET #(); True%I }}}.
Proof.
   wp_start. wp_auto_lc 3. iNamed "Hpre".
   iAssert (∃ (received: gmultiset streamold.t) (s_val: streamold.t),
    "s" ∷ s_ptr ↦ s_val ∗
    "Hcons" ∷ mpmc_consumer γmpmc received
  )%I with "[s Hcons]" as "IH".
  { iExists ∅, _. iFrame. }

  wp_for "IH".
    wp_apply (@wp_mpmc_receive with "[$Hcons]").
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
Proof using contributionG0 dspG0 W.
  wp_start. wp_auto.
  wp_apply chan.wp_make2; [done|].
  iIntros (c γ) "(#Hic & _ & Hoc)". wp_auto.
  iMod (start_mpmc _ _ _ _ 1 1 with "Hic Hoc") as (γmpmc) "[#Hmpmc [[Hprod _] [Hcons _]]]";
    [done|lia..|].
  wp_apply (wp_fork with "[Hcons]").
  { wp_apply (wp_Muxer with "[Hcons]"); [|done]. iFrame "Hmpmc Hcons". }
  wp_apply (wp_mkStream _ (λ _, True)%I (λ s1 s2, ⌜s2 = s1 ++ ","%go⌝)%I).
  { iIntros (s) "!> _". wp_auto. by eauto. }
  iIntros (γ1 stream1) "[Hstream1 Hc1]".
  wp_auto.
  wp_apply (wp_mkStream _ (λ _, True)%I (λ s1 s2, ⌜s2 = s1 ++ "!"%go⌝)%I).
  { iIntros (s) "!> _". wp_auto. by eauto. }
  iIntros (γ2 stream2) "[Hstream2 Hc2]".
  wp_auto.
  wp_apply (@wp_mpmc_send with "[$Hmpmc $Hprod $Hstream1]").
  iIntros "Hprod".
  wp_auto.
  wp_apply (@wp_mpmc_send with "[$Hmpmc $Hprod $Hstream2]").
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

Section notready_examples.

Lemma wp_select_no_double_close :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.select_no_double_close #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  wp_apply chan.wp_make1.
  iIntros "* (#His_ch & %Hcap & Hch)". simpl.
  wp_auto.
  wp_apply (chan.wp_close with "[$]").
  iIntros "_". iApply fupd_mask_intro; first solve_ndisj.
  iIntros "Hmask". iFrame. iNext. iIntros "Hch". iMod "Hmask" as "_". iModIntro.
  wp_auto.
  wp_apply (chan.wp_select_nonblocking_alt [False%I] with "[Hch] [-]");
    [|iNamedAccu|].
  - simpl. iSplitL; last done. repeat iExists _; iSplitR; first done. iFrame "#".
    iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
    iFrame. iIntros "!> Hch". iMod "Hmask" as "_". iModIntro.
    iNamed 1. wp_auto. by iApply "HΦ".
  - iNamed 1. simpl. iIntros ([[]]).
Qed.

End notready_examples.

Section exchange_pointer_proof.

Lemma wp_exchangePointer :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.exchangePointer #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  wp_apply chan.wp_make1.
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
  
  iMod (start_handoff result1_ch γr1 (λ v, ⌜v = W64 6⌝)%I with "Hr1_is_chan Hr1_own") 
    as (γh1) "[%Heq1 #Hhandoff1]".
  iMod (start_handoff result2_ch γr2 (λ v, ⌜v = W64 10⌝)%I with "Hr2_is_chan Hr2_own")
    as (γh2) "[%Heq2 #Hhandoff2]".
  
  iMod (start_done_with_broadcast_notified (V:=unit) (t:=go.StructType []) done_ch γdone (sharedValue_ptr ↦□ W64 2)%I with "Hdone_is_chan Hdone_own")
    as (γbc) "(#Hbc & HBcastNotif & #HBc)".

  iPersist "done result1 result2".
  
  wp_apply (wp_fork with "[result1 result2 done]").
  {
    rename done_ch into done_ch_1.
    wp_auto_lc 1.
    wp_apply ((wp_done_receive_broadcast (V:=unit) (t:=go.StructType []) γbc done_ch_1 ((sharedValue_ptr ↦□ W64 2)%I))  with "[$Hbc]").
    {
      iFrame "#".
    }

    iIntros "HShared".
    wp_auto.
    wp_apply (wp_handoff_send with "[$Hhandoff1]").
    { iPureIntro. word. }
    done.
  }

   wp_apply (wp_fork with "[result1 result2 done]").
  {
    rename done_ch into done_ch_1.
    wp_auto_lc 1.
    wp_apply ((wp_done_receive_broadcast (V:=unit) (t:=go.StructType []) γbc done_ch_1  ((sharedValue_ptr ↦□ W64 2)%I))
    with "[$Hbc]").
    {
      iFrame "#".
    }

    iIntros "HShared".
    wp_auto.
    wp_apply (wp_handoff_send with "[$Hhandoff2]").
    { iPureIntro. word. }
    done.
  }
  iPersist "sharedValue".

  wp_apply ((wp_done_close (V:=unit) (t:=go.StructType []) γbc done_ch ( ((sharedValue_ptr ↦□ W64 2)%I))) with "[Hbc HBcastNotif]").
  {
    iFrame "#". iFrame.
  }
  wp_apply (wp_handoff_receive with "Hhandoff1").
  iIntros (v1) "%Hv1". subst v1.
  wp_auto.
  wp_apply (wp_handoff_receive with "Hhandoff2").
  iIntros (v2) "%Hv2". subst v2.
  wp_auto.
  iApply "HΦ". done.
Qed.

End broadcast_example_proof.

Section google_example.

Context `{!chan_idiomG Σ go_string}.
Context `{!ghost_map.ghost_mapG Σ gname (go_string → iProp Σ)}.
  #[local] Existing Instance H.
Context `{!inG Σ unitR}.

Lemma wp_Web (q : go_string) :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.Web #q
  {{{ RET #(q ++ ".html"%go); True }}}.
Proof. wp_start. wp_auto. iApply "HΦ". done. Qed.

Lemma wp_Image (q : go_string) :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.Image #q
  {{{ RET #(q ++ ".png"%go); True }}}.
Proof. wp_start. wp_auto. iApply "HΦ". done. Qed.

Lemma wp_Video (q : go_string) :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.Video #q
  {{{ RET #(q ++ ".mp4"%go); True }}}.
Proof. wp_start. wp_auto. iApply "HΦ". done. Qed.


Definition google_expected (q: go_string) : list go_string :=
  [ q ++ ".html"%go; q ++ ".png"%go; q ++ ".mp4"%go ].


Inductive kind := KWeb | KImg | KVid.

Definition kind_eq_dec : ∀ x y : kind, {x = y} + {x ≠ y}.
Proof. decide equality. Defined.

Definition value_of (q:go_string) (k:kind) : go_string :=
  match k with
  | KWeb => q ++ ".html"%go
  | KImg => q ++ ".png"%go
  | KVid => q ++ ".mp4"%go
  end.

Definition pure_contract_of (q:go_string) (k:kind) : go_string → Prop :=
  λ v, v = value_of q k.

Definition contract_of (q:go_string) (k:kind) : go_string → iProp Σ :=
  λ v, ⌜pure_contract_of q k v⌝%I.

Lemma pure_contract_of_inj (q:go_string) (k1 k2:kind) :
  pure_contract_of q k1 = pure_contract_of q k2 → k1 = k2.
Proof.
  
  intro Heq.
  destruct k1, k2; try done.
  all: exfalso.
  all: 
    set v := value_of q KWeb.
    {
    have Heqv : pure_contract_of q KWeb v = pure_contract_of q KImg v by (exact (f_equal (fun f => f v) Heq)).
    rewrite /pure_contract_of in Heqv.
     subst v.
  unfold value_of in Heqv.

  symmetry in Heqv.
  assert (q ++ ".html"%go ≠ q ++ ".png"%go).
  {
   destruct q.
   {
    set_solver.
   }
   set_solver. 
  }
  {
    assert ((q ++ ".html"%go = q ++ ".html"%go)).
    {
      done.
    }
  assert (q ++ ".html"%go = q ++ ".png"%go).
  { rewrite Heqv. reflexivity. }
  congruence.
  }
    }
      {
    have Heqv : pure_contract_of q KWeb v = pure_contract_of q KVid v by (exact (f_equal (fun f => f v) Heq)).
    rewrite /pure_contract_of in Heqv.
     subst v.
  unfold value_of in Heqv.

  symmetry in Heqv.
  assert (q ++ ".html"%go ≠ q ++ ".mp4"%go).
  {
   destruct q.
   {
    set_solver.
   }
   set_solver. 
  }
  {
    assert ((q ++ ".html"%go = q ++ ".html"%go)).
    {
      done.
    }
  assert (q ++ ".html"%go = q ++ ".mp4"%go).
  { rewrite Heqv. reflexivity. }
  congruence.
  }
    }
    {
    have Heqv : pure_contract_of q KImg v = pure_contract_of q KWeb v by (exact (f_equal (fun f => f v) Heq)).
    rewrite /pure_contract_of in Heqv.
     subst v.
  unfold value_of in Heqv.

  symmetry in Heqv.
  assert (q ++ ".html"%go ≠ q ++ ".png"%go).
  {
   destruct q.
   {
    set_solver.
   }
   set_solver. 
  }
  {
    assert ((q ++ ".html"%go = q ++ ".html"%go)).
    {
      done.
    }
  assert (q ++ ".html"%go = q ++ ".png"%go).
  { 
    rewrite Heqv in H1.
  done.
  }
  congruence.
  }

    }

       {
  unfold pure_contract_of in Heq.
  assert (value_of q KImg = value_of q KVid) as Hbad.
  { apply (f_equal (fun f => f (value_of q KImg))) in Heq.
    unfold value_of in Heq. simpl in Heq.
    symmetry in Heq.
    assert (q ++ ".png"%go = q ++ ".mp4"%go).
    { rewrite Heq. reflexivity. }
    assumption.
  }
  
  unfold value_of in Hbad. simpl in Hbad.
  
  assert (q ++ ".png"%go ≠ q ++ ".mp4"%go).
  { intros Heq_bad.
    set_solver.
  }
  congruence.
       }
         {
  unfold pure_contract_of in Heq.
  
  assert (value_of q KVid = value_of q KWeb) as Hbad.
  { apply (f_equal (fun f => f (value_of q KVid))) in Heq.
    unfold value_of in Heq. simpl in Heq.
    symmetry in Heq.
    assert (q ++ ".mp4"%go = q ++ ".html"%go).
    { rewrite Heq. reflexivity. }
    assumption.
  }
  
  unfold value_of in Hbad. simpl in Hbad.
  assert (q ++ ".mp4"%go ≠ q ++ ".html"%go).
  { intros Heq_bad.
    set_solver.
  }
  congruence.
       }
        {
  unfold pure_contract_of in Heq.
  
  assert (value_of q KVid = value_of q KImg) as Hbad.
  { apply (f_equal (fun f => f (value_of q KVid))) in Heq.
    unfold value_of in Heq. simpl in Heq.
    symmetry in Heq.
    assert (q ++ ".mp4"%go = q ++ ".png"%go).
    { rewrite Heq. reflexivity. }
    assumption.
  }
  
  unfold value_of in Hbad. simpl in Hbad.
  assert (q ++ ".mp4"%go ≠ q ++ ".png"%go).
  { intros Heq_bad.
    set_solver.
  }
  congruence.
       }
Qed.

Definition pendingk : list kind := [KWeb; KImg; KVid].

Lemma pendingk_nodup : NoDup pendingk.
Proof. unfold pendingk. repeat constructor; set_solver. Qed.

Lemma contract_of_sound (q:go_string) (k:kind) (v:go_string) :
  contract_of q k v ⊢ ⌜v = value_of q k⌝.
Proof. iIntros "%Hv". iPureIntro. exact Hv. Qed.

Lemma mem_map_contract_of (q:go_string) (remk:list kind) (P:go_string→iProp Σ) :
  P ∈ map (contract_of q) remk →
  ∃ k, k ∈ remk ∧ P = contract_of q k.
Proof.
  intro HP.
  rewrite -(list_fmap_map (contract_of q) remk) in HP.
  apply (proj1 (list_elem_of_fmap _ _ _)) in HP.
  destruct HP as (k & -> & Hk). eauto.
Qed.

Lemma delete_middle {A} (l1 : list A) (x : A) (l2 : list A) :
  delete (length l1) (l1 ++ x :: l2) = l1 ++ l2.
Proof.
  induction l1 as [|a l1 IH]; simpl; [done|].
  by rewrite IH.
Qed.

Lemma wp_Google (q : go_string) :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.Google #q
  {{{ (sl : slice.t), RET #sl;
      ∃ xs, sl ↦* xs ∗ ⌜xs ≡ₚ google_expected q⌝ }}}.
Proof using All.
  wp_start.
  wp_auto.

  wp_apply (chan.wp_make2 (W64 3)); first done.
  iIntros (c γch) "(#Hchan & %Hcap3 & Hown)".
  simpl in *.

  iMod (start_future
          (V:=go_string)
          (t:=go.string)
          (ghost_mapG0:=H)
          c γch (chanstate.Buffered [])
        with "[$Hchan] [$Hown]") as (γmf) "(#Hmf & HAwait)".
  { right. done. }

  wp_auto.

  iMod (future_alloc_promise (t:=go.string) γmf c (contract_of q KWeb) []
        with "[$Hmf] [$HAwait]") as "(Hprom_web & HAwait)".
  iMod (future_alloc_promise (t:=go.string) γmf c (contract_of q KImg) _
        with "[$Hmf] [$HAwait]") as "(Hprom_img & HAwait)".
  iMod (future_alloc_promise (t:=go.string) γmf c (contract_of q KVid) _
        with "[$Hmf] [$HAwait]") as "(Hprom_vid & HAwait)".

  simpl.
  iPersist "c query".

  wp_apply (wp_fork with "[Hprom_web]").
  {
    wp_auto.
    wp_apply (wp_Web q).
    wp_apply (wp_future_fulfill
                (V:=go_string)
                (t:=go.string)
                (ghost_mapG0:=H)
                γmf c (value_of q KWeb)
              with "[$Hmf $Hprom_web]").
    { iPureIntro. reflexivity. }
    done.
  }

  wp_apply (wp_fork with "[Hprom_img]").
  {
    wp_auto.
    wp_apply (wp_Image q).
    wp_apply (wp_future_fulfill
                (V:=go_string)
                (t:=go.string)
                (ghost_mapG0:=H)
                γmf c (value_of q KImg)
              with "[$Hmf $Hprom_img]").
    { iPureIntro. reflexivity. }
    done.
  }

  wp_apply (wp_fork with "[Hprom_vid]").
  {
    wp_auto.
    wp_apply (wp_Video q).
    wp_apply (wp_future_fulfill
                (V:=go_string)
                (t:=go.string)
                (ghost_mapG0:=H)
                γmf c (value_of q KVid)
              with "[$Hmf $Hprom_vid]").
    { iPureIntro. reflexivity. }
    done.
  }

  wp_apply (wp_slice_make3 (V:=go_string) (t:=go.string)).
  { word. }

  iIntros (sl) "[Hsl [Hcap_sl %Hcap]]".
  wp_auto.

  iAssert (∃ (i : nat) (xs : list go_string)
                  (donek remk : list kind) (sl0 : slice.t),
      "i"            ∷ i_ptr ↦ W64 i ∗
      "results"      ∷ results_ptr ↦ sl0 ∗
      "Hsl"          ∷ sl0 ↦* xs ∗
      "Hcap"         ∷ own_slice_cap go_string sl0 (DfracOwn 1) ∗
      "HAwait"       ∷ Await (V:=go_string) γmf (map (contract_of q) remk) ∗
      "%Hlen"        ∷ ⌜length xs = i⌝ ∗
      "%Hi"          ∷ ⌜i ≤ 3⌝ ∗
      "%Hrem"        ∷ ⌜length remk = 3 - i⌝ ∗
      "%Hnodup_rem"  ∷ ⌜NoDup remk⌝ ∗
      "%Hsplit"      ∷ ⌜pendingk ≡ₚ donek ++ remk⌝ ∗
      "%Hperm"       ∷ ⌜xs ≡ₚ map (value_of q) donek⌝
    )%I
    with "[i results Hsl Hcap_sl HAwait]" as "IH".
  {
    iFrame.
    iExists 0.
    iExists ([] : list kind).
    iFrame.
    iExists ([KWeb; KImg; KVid]).
    iSplitL "HAwait".
    { iNamedAccu. }
    iFrame.
    repeat (iSplit; [iPureIntro; try reflexivity; try lia;
                     auto using pendingk_nodup|]).
    iPureIntro. simpl. reflexivity.
  }

  wp_for "IH".
  wp_if_destruct.

  - wp_apply (wp_future_await
                (V:=go_string)
                (t:=go.string)
                (ghost_mapG0:=H)
                γmf c (map (contract_of q) remk)
              with "[$Hmf HAwait]").
    { iNamedAccu. }

    iIntros (v P pre post) "(%HsplitP & HPv & HAwait')".

    have HPmem : P ∈ map (contract_of q) remk
      by (rewrite HsplitP; set_solver).
    destruct (mem_map_contract_of q remk P HPmem)
      as (k & Hkin & ->).
    iDestruct (contract_of_sound q k v with "HPv") as %->.

    wp_auto.

    wp_apply wp_slice_literal as "% Hsl1".
    { iIntros. wp_auto. iFrame. }

    wp_apply (wp_slice_append with "[$Hsl $Hcap $Hsl1]").
    iIntros (sl') "[Hsl' Hcap']".
    wp_auto.

    set j := length pre.
    set remk' := delete j remk.

    have Hj_lt_map : j < length (map (contract_of q) remk).
    {
      subst j.
      rewrite HsplitP.
      rewrite app_length /=.
      lia.
    }

    have Hj_lt : j < length remk.
    {
      rewrite length_map in Hj_lt_map.
      done.
    }

    have Hlook_map :
      (map (contract_of q) remk) !! j = Some (contract_of q k).
    {
      subst j.
      rewrite HsplitP.
      rewrite lookup_app_r; last lia.
      replace (length pre - length pre) with 0 by lia.
      simpl. done.
    }

    apply (list_lookup_fmap_Some
             (contract_of q) remk j (contract_of q k))
      in Hlook_map as (k0 & Hk0 & Hk0eq).

    apply (f_equal (fun f => f (value_of q k0))) in Hk0.
    simpl in Hk0.

    iAssert (⌜value_of q k0 = value_of q k⌝)%I as "%Hbad".
    {
      unfold contract_of, pure_contract_of in Hk0.
      iEval (rewrite Hk0). done.
    }

    have Heq_k0_k : k0 = k.
    {
      apply (pure_contract_of_inj q).
      unfold contract_of, pure_contract_of in Hk0.
      unfold contract_of, pure_contract_of.
      rewrite Hbad.
      done.
    }

    have Hlook_remk : remk !! j = Some k
      by (replace k with k0 by done; done).

    have Hdecomp :
      take j remk ++ k :: drop (S j) remk = remk
      by exact (take_drop_middle remk j k Hlook_remk).

    have Hrem' : length remk' = 3 - S (length xs).
    {
      rewrite /remk' length_delete;
        [|by apply lookup_lt_is_Some_2].
      lia.
    }

    have Hmap_remk' :
      map (contract_of q) remk' = pre ++ post.
    {
      subst remk' j.
      rewrite -!list_fmap_map list_fmap_delete list_fmap_map.
      rewrite HsplitP delete_middle.
      done.
    }

    set donek' := donek ++ [k].

    have Hsplit' :
      pendingk ≡ₚ donek' ++ remk'.
    {
      unfold donek', remk'.
      subst j.
      eapply Permutation_trans; [exact Hsplit|].
      rewrite (delete_take_drop remk) -Hdecomp.
      repeat rewrite -app_assoc.
      simpl.
      apply Permutation_app_head.
      rewrite Permutation_middle Hdecomp.
      rewrite Hdecomp.
      done.
    }

    have Hperm' :
      (xs ++ [value_of q k]) ≡ₚ map (value_of q) donek'.
    {
      unfold donek'.
      rewrite map_app /=.
      etransitivity; [|reflexivity].
      rewrite Hperm.
      reflexivity.
    }

    have Hnodup_rem' : NoDup remk'.
    {
      apply (sublist_NoDup _ _ Hnodup_rem).
      apply sublist_delete.
    }

    wp_for_post.
    iFrame "HΦ".
    iExists (S (length xs)),
            (xs ++ [value_of q k]),
            donek', remk', sl'.
    iFrame "#%".
    iFrame.

    iSplitL "i".
    {
      replace (W64 (S (length xs)))
        with (w64_word_instance.(word.add)
                (W64 (length xs)) (W64 1))
        by word.
      done.
    }

    iDestruct "Hcap'" as "[Hcap Hsl]".
    iFrame.

    iSplitL "HAwait'".
    { rewrite Hmap_remk'. done. }

    repeat (iSplit;
            [iPureIntro;
             auto;
             try (rewrite length_app singleton_length; lia)|]).
    iPureIntro. lia.

  - iApply "HΦ".
    iExists xs.
    iFrame "Hsl".
    iPureIntro.

    have Hlenxs : length xs = 3.
    {
      have : ¬ length xs < 3 by (intro; apply n; word).
      lia.
    }

    have Hremk_nil : remk = [].
    {
      apply length_zero_iff_nil.
      rewrite Hrem.
      assert (length xs = 3) by exact Hlenxs.
      lia.
    }

    have Hdone : pendingk ≡ₚ donek.
    {
      subst remk.
      rewrite app_nil_r in Hsplit.
      done.
    }

    have Hmap :
      map (value_of q) pendingk ≡ₚ
      map (value_of q) donek :=
      Permutation_map (value_of q) Hdone.

    have Hexp :
      map (value_of q) pendingk = google_expected q.
    { reflexivity. }

    etransitivity; [exact Hperm|].
    eapply Permutation_trans.
    { exact (Permutation_sym Hmap). }
    rewrite Hexp.
    apply Permutation_refl.

    Unshelve.
    all: try (typeclasses eauto).
Qed.

End google_example.
End proof.
