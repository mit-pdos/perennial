From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_ghost_state chan_spec_base buffered_chan_helpers.
From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_spec_inv.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof Require Import proof_prelude.
Require Export New.code.sync.
Require Export New.generatedproof.sync.
From New.proof.sync_proof Require Import base mutex sema.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!goGlobalsGS Σ}.
Context  `{!chanGhostStateG Σ}.

Notation "vs1 =?= vs2" := (valid_chan_state_eq vs1 vs2) (at level 70).
Arguments ch_loc: default implicits.
Arguments ch_mu: default implicits.
Arguments ch_buff: default implicits.
Arguments ch_γ: default implicits.
Arguments ch_size: default implicits.
Arguments ch_is_single_party: default implicits.
Arguments ch_Psingle: default implicits.
Arguments ch_Qsingle: default implicits.
Arguments ch_Qmulti: default implicits.
Arguments ch_Pmulti: default implicits.
Arguments ch_R: default implicits.

  Lemma wp_Channel__BufferedTryReceiveLocked (V: Type) {K: IntoVal V} {t: go_type} {H': IntoValTyped V t}  (params: chan V) (i: nat) (q: Qp) (Ri: nat -> iProp Σ):
  (ch_loc params) ≠ null ->
  (if (ch_is_single_party params) then (q) = 1%Qp else (q ≤ 1)%Qp) ->
  (ch_size params) > 0 ->  (* Must be buffered *)
  {{{ is_pkg_init channel ∗ recv_pre_inner V params q i Ri  }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "BufferedTryReceiveLocked" #t #()
  {{{ (success: bool) (v: V) (has_value: bool), RET (#success, #v, #has_value);
      if success then
        if has_value then
          recv_post_inner V params q i true v Ri
        else
          (* Channel is closed, no value *)
          recv_post_inner V params q i false v Ri
      else
        (* Channel is empty but not closed *)
        recv_pre_inner V params q i Ri
  }}}.
Proof.
  intros  Hnn Hsp Hsize_pos.
  wp_start. wp_auto.
  rewrite -wp_fupd.
  
  iNamed "Hpre". iNamed "HCh".
  
  wp_auto.

  
  wp_if_destruct.
  { (* Buffer has data - receive it *)
    (* Extract buffer state *)
      (* First, establish the condition as a pure fact *)
    assert ((params.(ch_size) =? 0) = false) by word.
      replace (params.(ch_size) =? 0) with false. 
        replace (params .(ch_buff) .(slice.len_f)) with (W64 params .(ch_size)).
        assert (0 < count) by word.
    iNamed "HChanState".
        
      set (should_freeze := ((count =? 1) && (vs =?= Valid_closed))).
    wp_auto.
      wp_pure;first word.
    (* Get element from slice *)
        edestruct (list_lookup_lt xs (uint.nat first)) as [x Hlookup].
        { word. }

      assert ((params.(ch_size) =? 0) = false).
      {
       word. 
      }
      replace (params.(ch_size) =? 0) with false. 
        replace (params .(ch_buff) .(slice.len_f)) with (W64 params .(ch_size)).
        assert (0 < count) by word.
    wp_apply (wp_load_slice_elem with "[$HBuffSlice]").
    { iPureIntro. 
        done.
    }
    iIntros "HBuffSlice".
    wp_auto.
    (* Update logical state *)
    iMod (buff_dequeue_logical V params vs send_count recv_count count first xs   i Ri
          with "[HPs HQs HRcvCtrAuth HQ HRecvPerm]") as "Hpost". all:try lia;try done.
    { iFrame.
    unfold recv_ctr_frozen. assert ((send_count =? recv_count) = false) by lia.
    rewrite H3. destruct vs. all: iFrame;iPureIntro;done.
    }
    iNamed "Hpost".
    iModIntro.
    iApply "HΦ". 
    unfold recv_post_inner.
     destruct params.(ch_is_single_party).
      {
        (* Single-party case *)
        rewrite Hsp.
        iNamed "HRecvPerm".
        iDestruct "HRecvPerm" as "[Hrcf Hctf]".
        iDestruct (recv_counter_elem with "[$HRcvCtrAuth] [$Hrcf]") as "%Helem".
        unfold isBufferedChanLogical.
        iDestruct "HBuffChLogical" as "(%Hct & %Hsz & %Hnewsizeinv & HPs & HQs)".
        iFrame.
        replace ((w64_word_instance .(word.sub) (W64 count) (W64 1))) with (W64 (count - 1)) by word. 

       set new_first := word.modu (word.add first (W64 1)) (W64 params.(ch_size)).
        subst new_first.
        replace (params.(ch_size)) with (Z.of_nat (length xs)) by lia.
        replace recv_count with i by lia.
        iFrame. unfold recv_ctr_frozen.
        replace (i + 1)%nat with (S i) by lia.
        iFrame "Hrcf".
        assert ((length xs =? 0) = false) by lia.
        rewrite H3. iExists (count - 1)%nat.
        iFrame. replace (W64 (count - 1)) with (W64 (count - 1)%nat) by word.
        iFrame. unfold isBufferedChanLogical.
        replace (params.(ch_buff).(slice.len_f)) with (W64 (length xs)) by word.
        iFrame "HPs".
        replace (params.(ch_size)) with (Z.of_nat (length xs)) by lia.
        iFrame. replace (length xs - (count - 1)%nat) with (length xs - (count - 1)) by word.
        iFrame "HQs".
        iPureIntro. word.
      }
      {
        iNamed "HRecvPerm".
        iDestruct "HRecvPerm" as "[Hrcf Hctf]".
        iDestruct (recv_counter_lower with "[$HRcvCtrAuth] [$Hrcf]") as "%Helem".
        unfold isBufferedChanLogical.
        iDestruct "HBuffChLogical" as "(%Hct & %Hsz & %Hnewsizeinv & HPs & HQs)".
        iFrame.
        replace ((w64_word_instance .(word.sub) (W64 count) (W64 1))) with (W64 (count - 1)) by word. 

       set new_first := word.modu (word.add first (W64 1)) (W64 params.(ch_size)).
        subst new_first.
        replace (params.(ch_size)) with (Z.of_nat (length xs)) by lia.
        iFrame. unfold recv_ctr_frozen.
        replace (i + 1)%nat with (S i) by lia.
        iFrame "Hrcf".
        assert ((length xs =? 0) = false) by lia.
        rewrite H3. iExists (count - 1)%nat.
        iFrame. replace (W64 (count - 1)) with (W64 (count - 1)%nat) by word.
        iFrame. unfold isBufferedChanLogical.
        replace (params.(ch_buff).(slice.len_f)) with (W64 (length xs)) by word.
        iFrame "HPs".
        replace (params.(ch_size)) with (Z.of_nat (length xs)) by lia.
        iFrame. replace (length xs - (count - 1)%nat) with (length xs - (count - 1)) by word.
        iFrame "HQs".
        iPureIntro. word.
      }
  }
  {
    
   wp_auto_lc 3. wp_if_destruct.
   {
    
    assert (vs = Valid_closed).
    {
      destruct vs. all: done.
    }
    subst vs.
    iNamed "HCloseTokPostClose".
    wp_auto. iApply "HΦ".
    unfold send_ctr_frozen. unfold recv_ctr_frozen.
       assert ((params.(ch_size) =? 0) = false) by word.
      replace (params.(ch_size) =? 0) with false. 
      replace (params .(ch_buff) .(slice.len_f)) with (W64 params .(ch_size)).
      assert ((W64 count) = (W64 0)) by word.
    iNamed "HChanState".
     assert (count = 0%nat) by word.
    assert (send_count = recv_count) by lia.
    
    replace (send_count =? recv_count) with true by lia.
    iDestruct "HSndCtrAuth" as "#HSndCtrAuth".
    iDestruct "HRcvCtrAuth" as "#HRcvCtrAuth".
    unfold own_recv_perm. iNamed "HRecvPerm".
    iDestruct "HRecvPerm" as "[H1 H2]".
    iDestruct "HCloseTokPostClose" as "[Hct Hsf]".
         iDestruct (send_counter_elem with "[$HSndCtrAuth] [$Hsf]") as "%Hag2".
       iDestruct ((own_closed_tok_post_close_pop params.(ch_γ) recv_count γi Ri (close_tok_names)) with "[H2 Hct]") as ">Hct".
      
      {
       iFrame.
       subst n0. subst recv_count. iFrame.
      }
      iFrame. iFrame "#". subst recv_count. iFrame. iFrame "#".
      iDestruct "Hct" as "[Hct Hri]".
  iDestruct ((lc_fupd_elim_later _ ( Ri send_count)) with "[$] [Hri]") as ">Hri".
  {
   
  iFrame.
  }

    iSplitR "Hri".
    {
      iFrame. unfold recv_ctr_frozen.
      simpl. iFrame "#". 
      rewrite H. iFrame. replace (send_count =? send_count) with true by lia. iFrame "#".
      iSplitL "Hct". { iExists (close_tok_names ∖ {[γi]}). subst n0. iFrame. done. }
      iPureIntro. done.
    }
    {
     iSplitL ""; first done.
     iModIntro.  iFrame. 

    }
   }
   {
    wp_auto. iApply "HΦ". iFrame. iFrame "#". iPureIntro. done.
   }
  }
Qed.

Lemma wp_Channel__BufferedTryReceive  (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V)   (i: nat) (q: Qp) (Ri: nat->iProp Σ):
  params.(ch_loc) ≠ null ->
  (if params.(ch_is_single_party) then q = 1%Qp else (q ≤ 1)%Qp) ->
  params.(ch_size) > 0 ->  (* Must be buffered *)
  {{{ is_pkg_init channel ∗ recv_pre V params q i Ri }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "BufferedTryReceive" #t #()
  {{{ (success: bool) (v: V) (has_value: bool), RET (#success, #v, #has_value);
      if success then
        if has_value then
          recv_post V params q i true v Ri
        else
          (* Channel is closed, no value *)
          recv_post V params q i false v Ri
      else
        (* Channel is empty but not closed *)
        recv_pre V params q i Ri
  }}}.
Proof.
  intros  Hnn Hsp Hsize_pos.
  wp_start. wp_auto. 
  rewrite -wp_fupd.
  iNamed "Hpre". iNamed "HCh".
  wp_auto.
   wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[locked Hinv]".
  iNamed "Hinv". 
    wp_apply (wp_Channel__BufferedTryReceiveLocked with "[HQ HChanState HCloseTokPostClose count state first value HSndCtrAuth HRcvCtrAuth HRecvPerm]"). all: try done.
  {
    
  unfold recv_pre_inner. iFrame. iFrame "#". iPureIntro. 
  do 1 split;first done. set_solver.  }
  iIntros (success). iIntros (v0). iIntros (has_value). 
iIntros "IH". 
wp_auto.


destruct success.
{
  destruct has_value.
  {
    iNamed "IH".
    iNamed "HCh".
    wp_apply (wp_Mutex__Unlock with "[$Hlock HChanState HCloseTokPostClose count state first value HSndCtrAuth HRcvCtrAuth $locked]").
    {
iFrame.
    }
    iApply "HΦ". iFrame. done.
  }
  {
    
    iNamed "IH".
    iNamed "HCh".
    wp_apply (wp_Mutex__Unlock with "[$Hlock HChanState HCloseTokPostClose count state first value HSndCtrAuth HRcvCtrAuth $locked]").
    {
iFrame.
    }
    iApply "HΦ". iFrame.
    done.
  }
}
{
  
    iNamed "IH".
    iDestruct "IH" as "(%Hbz & _ & HQ & HRecvPerm)".
    iNamed "HCh".
    wp_apply (wp_Mutex__Unlock with "[$Hlock HChanState HCloseTokPostClose count state first value HSndCtrAuth HRcvCtrAuth $locked]").
    {
iFrame.
    }
    iApply "HΦ". iFrame.
    iFrame "#".
    iPureIntro. done.

}
Qed.

(* Define receiver transitions as an enum type *)
Inductive receiver_transition : Type :=
  | receiver_offer_trans      (* Valid_start → Valid_receiver_ready *)
  | receiver_complete_trans   (* Valid_sender_ready → Valid_receiver_done *)
  | receiver_rescind_trans    (* Valid_receiver_ready → Valid_start *)
  | receiver_complete_second_trans. (* Valid_sender_done → Valid_start *)

(* Define a relation that checks if a transition is valid between two states *)
Definition is_valid_recv_transition (tr: receiver_transition) (vs_old vs_new: valid_chan_state) : Prop :=
  match tr, vs_old, vs_new with
  | receiver_offer_trans, Valid_start, Valid_receiver_ready => True
  | receiver_complete_trans, Valid_sender_ready, Valid_receiver_done => True
  | receiver_rescind_trans, Valid_receiver_ready, Valid_start => True
  | receiver_complete_second_trans, Valid_sender_done, Valid_start => True
  | _, _, _ => False
  end.

(* Define how receiving count changes in each transition *)
Definition receiver_recv_count_change (tr: receiver_transition) : nat :=
  match tr with
  | receiver_complete_trans => 1
  | receiver_complete_second_trans => 1
  | _ => 0
  end.

(* Define whether additional token is needed for the transition *)
Definition receiver_needs_token (tr: receiver_transition) : bool :=
  match tr with
  | receiver_rescind_trans => true
  | receiver_complete_second_trans => true
  | _ => false
  end.

(* Define whether token is produced by the transition *)
Definition receiver_produces_token (tr: receiver_transition) : bool :=
  match tr with
  | receiver_offer_trans => true
  | _ => false
  end.

(* Define whether Q resource is needed for the transition *)
Definition receiver_needs_Q (tr: receiver_transition) : bool :=
  match tr with
  | receiver_offer_trans => true
  | receiver_complete_trans => true
  | _ => false
  end.

(* Define whether P resource is produced by the transition *)
Definition receiver_produces_P (tr: receiver_transition) : bool :=
  match tr with
  | receiver_complete_trans => true
  | receiver_complete_second_trans => true
  | _ => false
  end.
(* Define boolean equality for receiver transitions *)
Definition receiver_transition_eqb (tr1 tr2: receiver_transition) : bool :=
  match tr1, tr2 with
  | receiver_offer_trans, receiver_offer_trans => true
  | receiver_complete_trans, receiver_complete_trans => true
  | receiver_rescind_trans, receiver_rescind_trans => true
  | receiver_complete_second_trans, receiver_complete_second_trans => true
  | _, _ => false
  end.

(* Helper to check if transition updates the value *)
Definition receiver_updates_value (tr: receiver_transition) : bool :=
  match tr with
  | receiver_complete_trans => false
  | receiver_complete_second_trans => false
  | _ => false
  end.

Lemma receiver_transition_general (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V)  
  (v : V) (vs_old vs_new: valid_chan_state) (tr: receiver_transition) 
  (send_count recv_count: nat) (i: nat) (q: Qp) (Ri: nat->iProp Σ):
  is_valid_recv_transition tr vs_old vs_new ->
  (if params.(ch_is_single_party) then q = 1%Qp else (q ≤  1)%Qp) ->
  (if params.(ch_is_single_party) then i = recv_count else true) ->
  (* Resources *)
  "HCh" ∷ isUnbufferedChan V params v vs_old send_count recv_count ∗
  (if receiver_needs_token tr then "Hrttok'" ∷ receiver_exchange_token params.(ch_γ) else "Hemp" ∷ emp) ∗
  (if receiver_needs_Q tr then "HQ" ∷ Q V params.(ch_is_single_party) (Z.of_nat i) params.(ch_Qsingle) params.(ch_Qmulti) else emp) ∗
  "HRcvCtrAuth" ∷ own_recv_counter_auth params.(ch_γ) recv_count (recv_ctr_frozen vs_old send_count recv_count) ∗ 
  "HRecvPerm" ∷ own_recv_perm params.(ch_γ) q i Ri
  ==∗ 
  (* Result resources *)
  "HCh" ∷ isUnbufferedChan V params 
     (if receiver_updates_value tr then v else v) 
     vs_new 
     send_count
     (recv_count + receiver_recv_count_change tr) ∗
  (if negb (receiver_produces_P tr) && negb (receiver_needs_Q tr) 
   then "HQ" ∷ Q V params.(ch_is_single_party) (Z.of_nat i) params.(ch_Qsingle) params.(ch_Qmulti) else emp) ∗
  (if receiver_produces_token tr 
   then "Hrttok" ∷ receiver_exchange_token params.(ch_γ) else emp) ∗
  (if receiver_produces_P tr 
   then 
       "HP" ∷ P V params.(ch_is_single_party) (Z.of_nat i) v params.(ch_Psingle) params.(ch_Pmulti)
   else emp) ∗
  "HRcvCtrAuth" ∷ own_recv_counter_auth params.(ch_γ) 
     (recv_count + receiver_recv_count_change tr) 
     (recv_ctr_frozen vs_new send_count (recv_count + receiver_recv_count_change tr)) ∗ 
  "HRecvPerm" ∷ own_recv_perm params.(ch_γ) q 
     (i + receiver_recv_count_change tr) Ri.
  Proof.
  intros Hvalid Hsp Hsamet.
  iIntros "Hpre".
  iNamed "Hpre".
  
  (* First, destruct by transition type to handle each case specifically *)
  destruct tr; simpl in *; unfold is_valid_recv_transition in Hvalid.
  
  { (* Case: receiver_offer_trans - Valid_start → Valid_receiver_ready *)
    destruct vs_old, vs_new; try (exfalso; exact Hvalid).
    simpl in *.
    iNamed "Hpre".
    
    (* Split unbuffered channel into facts and resources *)
    unfold isUnbufferedChan.
    iDestruct "HCh" as "[%HChanFacts HChanRes]".
    
    (* Extract state resources *)
    iDestruct "HChanRes" as "Hfull".
    
    (* Handle token splitting to create receiver token *)
    iMod (receiver_exchange_token_split params.(ch_γ) with "Hfull") as "[Hrttok Hfull]".
    
    (* Handle counter verification *)
    unfold own_recv_perm. iNamed "HRecvPerm".
    iDestruct "HRecvPerm" as "[Hrcf Hctf]".
    iAssert (own_recv_counter_auth params.(ch_γ) recv_count false ∗ 
             own_recv_counter_frag params.(ch_γ) i q ∗ 
             ⌜if params.(ch_is_single_party) then recv_count = i else i ≤ recv_count⌝%I)%I
      with "[HRcvCtrAuth Hrcf]" as "(HRcvCtrAuth & HRecvPerm & %Hispz)".
    {
      destruct params.(ch_is_single_party).
      - 
      replace q with 1%Qp by done. 
        iDestruct (recv_counter_elem with "[$HRcvCtrAuth] [$Hrcf]") as "%Hag2".
        iFrame. iPureIntro. done.
      - iDestruct (recv_counter_lower with "[$HRcvCtrAuth] [$Hrcf]") as "%Hag2".
        iFrame. iPureIntro. lia.
    }
    
    (* Finalize *)
    iModIntro.
    unfold chan_state_resources.
    replace (recv_count + 0)%nat with recv_count by lia.
    replace (i + 0)%nat with i by lia.
    
    (* Rebuild resources *)
    iFrame "HRcvCtrAuth".
    iSplitL "Hrttok HQ".
    { (* Build new channel state *)
      unfold isUnbufferedChan.
      iSplitR; first done.
      unfold chan_state_resources. simpl.
      iFrame.
      destruct params.(ch_is_single_party).
      {
       subst i. done. 
      }
      unfold Q. 
      destruct bool_decide eqn: Hb.
      {
        apply bool_decide_eq_true in Hb.
        destruct bool_decide eqn: Hc; first done.
        { 
         lia.
        }
      }
      {
      apply bool_decide_eq_false in Hb.
       destruct bool_decide. all: done.
      }
    }
      {
    iFrame.
      } 
  }
  {
  iNamed "Hpre". iFrame.
  unfold isUnbufferedChan.
  iNamed "HCh".
  iDestruct "HCh" as "[Hf Hres]".
  unfold chan_state_resources.
  destruct vs_old eqn: H0, vs_new eqn: H1. all: try done;try (exfalso; apply Hvalid).
  { 
    iNamed "Hf". iNamed "Hres". 
      
    (* Get value from sender token *)
    unfold own_recv_perm. iNamed "HRecvPerm".
    iDestruct "HRecvPerm" as "[Hrcf Hctf]".
    iDestruct (recv_counter_update with "[$HRcvCtrAuth $Hrcf]") as ">[HRcvCtrAuth Hrcf]".
    replace (recv_count + 1)%nat with (S recv_count) by lia.
    replace (i + 1)%nat with (S i) by lia.
    iFrame.
    iSplitR "HP".
    {
      iSplitR "HQ".
      {
       iPureIntro. rewrite HUnBuffFacts. lia. 
      }
      destruct (params.(ch_is_single_party)).
      {

       iFrame.
       subst i. subst recv_count.
       done. 
      }
      {
        unfold Q.
        destruct bool_decide eqn: Houter.
        {
          apply bool_decide_eq_true in Houter.
          destruct bool_decide eqn: Hinner;first done.
          {
           lia.
          }
        }
       iFrame.
       apply bool_decide_eq_false in Houter. 
       destruct bool_decide. all: done.
      }
    }
    {
      destruct params.(ch_is_single_party).
      {
        subst i. subst send_count. iFrame. done.
      }
      iFrame.
      done.
    }
  }
  }
  {
    iNamed "Hpre". unfold isUnbufferedChan.
    iDestruct "HCh" as "[Hfacts Hres]".
   iFrame.
   destruct vs_old, vs_new. all: try done.
   iFrame.
   iNamed "Hres".
   iNamed "Hfacts".
   iNamed "Hpre". iDestruct "Hpre" as "[_ Hpre]".
   iNamed "Hpre".
   replace (i + 0)%nat with i by lia. iFrame.
   replace (recv_count + 0)%nat with recv_count by lia.
   iFrame. unfold chan_state_resources.
   iDestruct ((receiver_exchange_token_combine params.(ch_γ)) with "[$Hextok $Hrttok']") as ">Hnrc".
   iFrame. destruct params.(ch_is_single_party).
   {
    unfold Q. 
    destruct bool_decide eqn: Houter.
    {
      apply bool_decide_eq_true in Houter.
      destruct bool_decide eqn: Hb.
      {
       done. 
      }
      iFrame.
      destruct recv_count.
      {
       done. 
      }
      done.
    }
    apply bool_decide_eq_false in Houter.
    destruct bool_decide. all: iFrame.
    {
     unfold chan_state_facts. done. 
    }
    {
      subst i. iFrame.
      iPureIntro. done.
    }
   } 
   {
    unfold Q. 
    destruct bool_decide eqn: Houter.
    {
      apply bool_decide_eq_true in Houter.
      destruct bool_decide eqn: Hb.
      {
       done. 
      }
      iFrame.
      destruct recv_count.
      {
       done. 
      }
      done.
    }
    apply bool_decide_eq_false in Houter. 
    destruct bool_decide. all: iFrame.
    {
     iPureIntro. done. 
    }
    iFrame. done.
   }
  }
  {
    iNamed "Hpre".
    iDestruct "Hpre" as "(_ & Hrest)".
    iNamed "Hrest". unfold isUnbufferedChan.
    destruct vs_old, vs_new. all: try done.
     iNamed "HCh".  
    unfold own_recv_perm. iNamed "HRecvPerm".
    iDestruct "HRecvPerm" as "[Hrcf Hctf]".
    iDestruct (recv_counter_update with "[$HRcvCtrAuth $Hrcf]") as ">[HRcvCtrAuth Hrcf]".
    replace (recv_count + 1)%nat with (S recv_count) by lia.
    replace (i + 1)%nat with (S i) by lia.
    iFrame.
   iDestruct ((receiver_exchange_token_combine params.(ch_γ)) with "[$Hextok $Hrttok']") as ">Hnrc".
   iFrame. 
   destruct (params.(ch_is_single_party)).
   {
    iFrame.
    subst i. iFrame. iPureIntro. done.
   }
   {
    iFrame. done.
   }
  }
  Qed.

Lemma wp_Channel__UnbufferedTryReceive (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V)  (i: nat) (q: Qp) (Ri: nat->iProp Σ):
  params.(ch_loc) ≠ null ->
  (if params.(ch_is_single_party) then q = 1%Qp else (q ≤  1)%Qp) ->
  params.(ch_size) = 0 ->  (* Must be unbuffered *)
  {{{ is_pkg_init channel ∗ recv_pre V params q i Ri }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "UnbufferedTryReceive" #t #()
  {{{ (selected: bool) (v: V) (ok: bool), RET (#selected, #v, #ok);
      if selected then
        recv_post V params q i ok v Ri
      else
        recv_pre V params q i Ri
  }}}.
intros Hvalid Hsp Hsame .
wp_start. wp_auto. iNamed "Hpre".
   iNamed "HCh".
   wp_auto.
      rewrite -wp_fupd.
   wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[locked Hinv]".
  iNamed "Hinv".
  iNamed "HRecvPerm".
  iDestruct "HRecvPerm" as "[Hrct Hctf]".
  rewrite Hsame. simpl.
  destruct vs.
  {
    wp_auto.
    iAssert (⌜ (if params.(ch_is_single_party) then i = recv_count else true) ⌝%I ) with "[HRcvCtrAuth Hrct]" as "%".
  {
   destruct params.(ch_is_single_party).
   {
    rewrite Hsp.
    iDestruct (recv_counter_elem with "[$HRcvCtrAuth] [$Hrct]") as "%Hag2";iPureIntro;done.
  }
  {
    iDestruct (recv_counter_lower with "[$HRcvCtrAuth] [$Hrct]") as "%Hag2";iPureIntro;done.
  }
  }
    iMod ((receiver_transition_general V params v Valid_start Valid_receiver_ready receiver_offer_trans send_count recv_count i)
      with "[HQ  HChanState Hrct Hctf HRcvCtrAuth ]") as 
      "IH".
      all: try done.
      {
       iFrame. 
      }
      {
       simpl. iNamed "IH". iDestruct "IH" as  "[_ Hrest]". iNamed "Hrest".
       iDestruct "Hrest" as "[_ Hrest]". iNamed "Hrest".
       wp_apply (wp_Mutex__Unlock with "[$Hlock HCloseTokPostClose HSndCtrAuth 
      first count value state HRcvCtrAuth HCh $locked]").
      {
        iFrame. 
      replace (recv_count + 0)%nat with recv_count by lia. 
      iFrame.
      replace (i + 0)%nat with i by lia.
        iFrame.
        iExists Valid_receiver_ready. iExists send_count. iExists recv_count.
        iFrame. rewrite Hsame. iFrame.
      }
      {
       wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[locked Hinv]".
      iNamed "Hinv".
      iNamed "HRecvPerm".
      iDestruct "HRecvPerm" as "[Hrct Hctf]".
    iAssert (⌜ (if params.(ch_is_single_party) then i = recv_count0 else true) ⌝%I ) with "[HRcvCtrAuth Hrct]" as "%".
  {
   destruct params.(ch_is_single_party).
   {
    rewrite Hsp0.
      replace (i + 0)%nat with i by lia.
    iDestruct (recv_counter_elem with "[$HRcvCtrAuth] [$Hrct]") as "%Hag2";iPureIntro;done.
  }
  {
    iDestruct (recv_counter_lower with "[$HRcvCtrAuth] [$Hrct]") as "%Hag2";iPureIntro;done.
  }
  }
      rewrite Hsame. simpl.
      destruct vs.
      {
        wp_auto.
        iNamed "HChanState".
        unfold chan_state_resources.
        iNamed "HChanState".
        unfold full_exchange_token.
        unfold receiver_exchange_token. iNamed "Hrttok".
        iCombine "Hextok" "Hrttok" as "Hcomb" gives "%Hinvalid".
        destruct Hinvalid as [Hiv1 Hiv2].
        done.
      }
      {
       iNamed "HChanState". 
      replace (i + 0)%nat with i by lia.
      wp_auto.
       iMod ((receiver_transition_general V params v Valid_receiver_ready Valid_start receiver_rescind_trans send_count0 recv_count0 i )
         with "[ HQ Hrttok  Hrct Hctf HRcvCtrAuth Hextok ]") as 
         "IH".
         all: try done.
         {
          iFrame. simpl.
          iPureIntro. done.
         }
         {
             simpl. 
      iNamed "IH".
      replace (recv_count + 0)%nat with recv_count by lia. 
      iFrame.
      replace (i + 0)%nat with i by lia.
      iDestruct "IH" as "(_ & _ &  Hrest)".
      iNamed "Hrest".  
   wp_apply (wp_Mutex__Unlock with "[$Hlock HCloseTokPostClose HSndCtrAuth 
    first count value state HRcvCtrAuth HCh $locked]").
    {
      iFrame.
      rewrite Hsame. iFrame.
      iExists Valid_start. iFrame.
    }
    iApply "HΦ". iFrame "#". iFrame. done.
      }
    }
    {
     wp_auto. 
      iNamed "HChanState".
        unfold chan_state_resources.
        unfold sender_exchange_token.
        unfold receiver_exchange_token. iNamed "Hrttok".
        iCombine "Hextok" "Hrttok" as "Hcomb" gives "%Hinvalid".
        destruct Hinvalid as [Hiv1 Hiv2].
        done.
    }
    {
      wp_auto.
      iNamed "HChanState".
        unfold chan_state_resources.
        unfold sender_exchange_token.
        unfold receiver_exchange_token. iNamed "Hrttok".
        iCombine "Hextok" "Hrttok" as "Hcomb" gives "%Hinvalid".
        destruct Hinvalid as [Hiv1 Hiv2].
        done.
    }
    {
      wp_auto.
      iNamed "HChanState".
    iMod ((receiver_transition_general V params v0 Valid_sender_done Valid_start receiver_complete_second_trans send_count0 recv_count0 i  )
      with "[Hrttok HP Hrct Hctf HRcvCtrAuth Hextok]") as 
      "IH".
      all: try done.
      {
      iFrame.  
      replace (i + 0)%nat with i by lia.
      iFrame. done.
      }
      {
        simpl. 
      iNamed "IH".
      replace (recv_count0 + 1)%nat with (S recv_count0) by lia. 
      iFrame.
      replace (i + 1)%nat with (S i) by lia.
      iDestruct "IH" as "(_ & _ &  Hrest)".
      iNamed "Hrest".  
   wp_apply (wp_Mutex__Unlock with "[$Hlock HCloseTokPostClose HSndCtrAuth 
    first count value state HRcvCtrAuth HCh $locked]").
    {
      iFrame.
      rewrite Hsame. iFrame.
    }
    iApply "HΦ". iFrame "#". iFrame.
      replace (i + 1)%nat with (S i) by lia.
    done.
      }
    }
      {
        wp_auto.
        iNamed "HCloseTokPostClose".
    subst.
    iDestruct "HCloseTokPostClose" as "[Hct Hscf]".
    iDestruct ((own_closed_tok_post_close_pop params.(ch_γ) n γi0 Ri (close_tok_names)) with "[$Hctf $Hct]") as ">Hct".
    unfold send_ctr_frozen. unfold recv_ctr_frozen.
    iNamed "HChanState". 
    replace (send_count0 =? recv_count0) with true by lia.
    iDestruct "HSndCtrAuth" as "#HSndCtrAuth".
    iDestruct "HRcvCtrAuth" as "#HRecvCtrAuth".
    iDestruct "Hct" as "[Hctpc HRi]".
    iDestruct (send_counter_elem with "[$HSndCtrAuth] [$Hscf]") as "%Hag2".
    wp_apply (wp_Mutex__Unlock with "[$Hlock HSndCtrAuth 
    first count value state HChanState Hctpc Hscf $locked]").
    {
      iFrame. iFrame "#". unfold recv_ctr_frozen. iExists recv_count0.
    replace (send_count0 =? recv_count0) with true by lia.
      iFrame "#".
      rewrite Hsame. iFrame. done.
    }
    {
     iApply "HΦ". iFrame. subst n. replace send_count0 with recv_count0.
     iFrame "#".
      replace (i + 0)%nat with i by lia.
      iFrame. 
     iPureIntro. done. 
    }

      }
      }

  }
  }

  {
   wp_auto.
   wp_apply (wp_Mutex__Unlock with "[$Hlock HCloseTokPostClose HSndCtrAuth 
    first count value state HRcvCtrAuth HChanState $locked]").
    {
      iFrame.
      rewrite Hsame. iFrame.
    }
    iApply "HΦ". iFrame "#". iFrame. iPureIntro. done.
  }
  {
    wp_auto.
     iAssert (⌜ (if params.(ch_is_single_party) then i = recv_count else true) ⌝%I ) with "[HRcvCtrAuth Hrct]" as "%".
  {
   destruct params.(ch_is_single_party).
   {
    rewrite Hsp0.
    iDestruct (recv_counter_elem with "[$HRcvCtrAuth] [$Hrct]") as "%Hag2";iPureIntro;done.
  }
  {
    iDestruct (recv_counter_lower with "[$HRcvCtrAuth] [$Hrct]") as "%Hag2";iPureIntro;done.
  }
  }
    iMod ((receiver_transition_general V params v Valid_sender_ready Valid_receiver_done receiver_complete_trans send_count recv_count i  )
      with "[HQ  Hrct HRcvCtrAuth Hctf HChanState ]") as 
      "IH".
      all: try done.
      {
      iFrame.  
      }
      {
        simpl. 
      iNamed "IH".
      replace (recv_count + 0)%nat with recv_count by lia. 
      iFrame.
      replace (i + 0)%nat with i by lia.
      iDestruct "IH" as "(_ & _ &  Hrest)".
      iNamed "Hrest".  
   wp_apply (wp_Mutex__Unlock with "[$Hlock HCloseTokPostClose HSndCtrAuth 
    first count value state HRcvCtrAuth HCh $locked]").
    {
      iFrame.
      rewrite Hsame. iFrame.
    }
    iApply "HΦ". iFrame "#". iFrame. done.
      }
  }
  {
    wp_auto.
   wp_apply (wp_Mutex__Unlock with "[$Hlock HCloseTokPostClose HSndCtrAuth 
    first count value state HRcvCtrAuth HChanState $locked]").
    {
      iFrame.
      rewrite Hsame. iFrame.
    }
    iApply "HΦ". iFrame "#". iFrame. iPureIntro. done.
  }
  {
   wp_auto.
   wp_apply (wp_Mutex__Unlock with "[$Hlock HCloseTokPostClose HSndCtrAuth 
    first count value state HRcvCtrAuth HChanState $locked]").
    {
      iFrame.
      rewrite Hsame. iFrame.
    }
    iApply "HΦ". iFrame "#". iFrame. iPureIntro. done.
  }
  {
    wp_auto.
    iNamed "HCloseTokPostClose".
    subst.
    iDestruct "HCloseTokPostClose" as "[Hct Hscf]".
    iDestruct ((own_closed_tok_post_close_pop params.(ch_γ) n γi Ri (close_tok_names)) with "[$Hctf $Hct]") as ">Hct".
    unfold send_ctr_frozen. unfold recv_ctr_frozen.
    iNamed "HChanState". 
    replace (send_count =? recv_count) with true by lia.
    iDestruct "HSndCtrAuth" as "#HSndCtrAuth".
    iDestruct "HRcvCtrAuth" as "#HRecvCtrAuth".
    iDestruct "Hct" as "[Hctpc HRi]".
    iDestruct (send_counter_elem with "[$HSndCtrAuth] [$Hscf]") as "%Hag2".
    wp_apply (wp_Mutex__Unlock with "[$Hlock HSndCtrAuth 
    first count value state HChanState Hctpc Hscf $locked]").
    {
      iFrame. iFrame "#". unfold recv_ctr_frozen. iExists recv_count.
    replace (send_count =? recv_count) with true by lia.
      iFrame "#".
      rewrite Hsame. iFrame. done.
    }
    {
     iApply "HΦ". iFrame. subst n. replace send_count with recv_count.
     iFrame "#". iPureIntro. done. 
    }
  }
Qed.
 
Lemma wp_Channel__TryReceive (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V)   (i: nat) (q: Qp) (Ri: nat->iProp Σ):
     
      (if params.(ch_is_single_party) then q = 1%Qp else (q ≤  1)%Qp) ->
      {{{ is_pkg_init channel ∗ recv_pre V params q i Ri }}}
        params.(ch_loc) @ channel @ "Channel'ptr" @ "TryReceive" #t #()
      {{{ (v: V) (ok selected: bool), RET (#selected, #v, #ok);
          if selected then
            recv_post V params q i ok v Ri
          else
            recv_pre V params q i Ri
      }}}.
    Proof. 
  intros Hsp.
  wp_start. wp_auto.
  iNamed "Hpre". iNamed "HCh". wp_auto.
  iDestruct (chan_pointsto_non_null V (params.(ch_mu)) params with "mu") as %HNonNull.
  assert (params .(ch_loc) ≠ null).
  {
    intro H1.
    rewrite H1 in HNonNull. done.
  }
  wp_if_destruct.  
  {
   wp_auto.
    wp_apply (wp_Channel__BufferedTryReceive V params i q Ri with "[HQ HRecvPerm]"). all: try done;try word.
    {
     assert ((params .(ch_buff) .(slice.len_f)) = (W64 params .(ch_size))).
     {
      apply to_val_inj in Hbuffsize.
      done.
     }
     word. 
    }
    {
     iFrame. iFrame "#". iPureIntro. done. 
    }
  iIntros (success). iIntros (v0). iIntros (has_value). 
iIntros "IH". 
wp_auto.
iApply "HΦ". 
destruct success.
{
  destruct has_value.
  {
    iFrame.
  }
  {
    iFrame.
  } 
}
iFrame.
  }
  {
    wp_auto.
    wp_apply (wp_Channel__UnbufferedTryReceive V params i q Ri with "[HQ HRecvPerm]"). all: try done;try word.
    {
       assert ((params .(ch_buff) .(slice.len_f)) = (W64 params .(ch_size))).
     {
      apply to_val_inj in Hbuffsize.
      done.
     }
     word. 
    }
    {
     iFrame. iFrame "#". done.
    }
    {
  iIntros (success). iIntros (v0). iIntros (has_value). 
iIntros "IH". 
wp_auto.
iApply "HΦ". 
destruct success.
{
  destruct has_value.
  {
    iFrame.
  }
  {
    iFrame.
  } 
}
done.
    }
  }
    Qed.

End proof.
