From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_ghost_state chan_spec_inv chan_spec_base buffered_chan_helpers.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof Require Import proof_prelude.
Require Export New.code.sync.
Require Export New.generatedproof.sync.
From New.proof.sync_proof Require Import base mutex sema.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!goGlobalsGS Σ}.
Context  `{!chanGhostStateG Σ}.

Implicit Types (v:val). 

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

Lemma wp_Channel__BufferedTrySend_params
  (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V) (q: Qp)   (i: nat) (v: V) :
  (if params.(ch_is_single_party) then q = 1%Qp else (q ≤ 1)%Qp) ->
 
  params.(ch_loc) ≠ null ->
  {{{ is_pkg_init channel ∗  send_pre_inner V params q i v  }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "BufferedTrySend" #t #v
  {{{ (success: bool), RET #success;
      if success then
        send_post_inner V params q i
      else
        send_pre_inner V params q i v
  }}}.
Proof.
  intros Hsp  Hnn . 
  let x := ident:(Φ) in
  try clear x.
  iIntros (Φ) "Hpre HΦ".
  destruct_pkg_init "Hpre".
  try (first [ wp_func_call | wp_method_call ]; wp_call; [idtac]).
  rewrite -wp_fupd.
  wp_auto_lc 1. iDestruct "Hpre" as "[Hpre Hmu]". iNamed "Hpre". iNamed "Hmu".
  iNamed "HCh".
  wp_auto.

  wp_if_destruct.
  {
    destruct vs. all: try done.
    iNamed "HCloseTokPostClose".
      iDestruct "HCloseTokPostClose" as "[HCloseTokPost HSendCtrFrag]".
      iCombine "HSendCtrFrag" "HSc" as "H" gives "%Hvalid". 
     apply auth_frag_op_valid_1 in Hvalid.
               rewrite <- (Some_op (1%Qp, n) (q, i)) in Hvalid.
               rewrite Some_valid in Hvalid.
               rewrite <- (pair_op 1%Qp q n i) in Hvalid.
               rewrite pair_valid in Hvalid. destruct Hvalid as [Hqvalid Hivalid].
               rewrite frac_op in Hqvalid.

               assert (((1 + q)%Qp ≤ 1)%Qp).
               { 
                done. 
               }
               apply Qp.not_add_le_l in H.
               contradiction.
  }
  wp_auto. 
  wp_if_destruct.
  { wp_auto.
      (* Locate target index in slice *)
      set (idx := uint.nat (word.modu (word.add first (word.unsigned count)) (params .(ch_buff) .(slice.len_f)))).
      assert ((params.(ch_size) =? 0) = false).
      {
       word. 
      }
      replace (params.(ch_size) =? 0) with false. 
      iNamed "HChanState".
      wp_pure;first word.
      wp_apply (wp_store_slice_elem with "[$HBuffSlice]").
      {
        replace (params .(ch_buff) .(slice.len_f)) with (W64 params .(ch_size)).
        {
         iPureIntro. word. 
        }
      }
      iIntros "Hslice".
      wp_auto.


      (* Build assertion for counter elements *)
      iAssert (own_send_counter_auth params.(ch_γ) send_count false ∗ 
      own_send_counter_frag params.(ch_γ) i q ∗ 
      ⌜if params.(ch_is_single_party) then send_count = i else i <= send_count⌝%I)%I 
      with "[HSndCtrAuth HSc]" as "(HSndCtrAuth & HSen & %Hispz)".
      {
      destruct params.(ch_is_single_party).
      - replace (q) with 1%Qp.
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSc]") as "%Hag2".
        iFrame.
        destruct vs. all:try (iFrame;done).
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSc]") as "%Hag2".  
       
       unfold send_ctr_frozen. destruct vs. all: try (iFrame;done);try (iFrame;iPureIntro;lia).
      }
      
      (* Set the new buffer state *)
      set (new_xs := <[idx:=v]> xs).
      iMod (buff_enqueue_logical V params vs send_count recv_count count first xs new_xs v i 
      with "[ HPs HQs HP HSndCtrAuth HSen]") as 
      "IH". all: (try done;try word).
      {
        subst idx.
        subst new_xs.
        replace (W64 (uint.Z (W64 count))) with (W64 count) by word.
        replace ((W64 (uint.Z (W64 params.(ch_size))))) with (W64 params.(ch_size)) by word.
        replace (params .(ch_buff) .(slice.len_f)) with (W64 params.(ch_size)).

        exact.
      }
      { 
       iFrame. iPureIntro. word.
      }
      iModIntro. iApply "HΦ".
      unfold send_post_inner. unfold isChanInner.
       iNamed "IH". 
            (* First, replace count + 1 with S count *)
      replace (count + 1)%nat with (S count)%nat by lia.

      (* Replace word.add (W64 count) (W64 1) with W64 (S count) *)
      replace (w64_word_instance.(word.add) (W64 count) (W64 1)) with (W64 (S count)) by word.
        iFrame "value first count state".
        iSplitR "HQ HSndPerm".
        {
        iExists (send_count + 1)%nat.
        iFrame. iExists (recv_count). iFrame. simpl.
        replace (params.(ch_size) =? 0) with false by lia.
        unfold recv_ctr_frozen.
        assert (vs ≠ Valid_closed).
        {
         destruct vs. all: try done. 
        }

        destruct vs. all: try (iFrame;done).
        {
         iFrame. subst new_xs. subst idx. iFrame. 
      replace ((W64 (uint.Z (W64 count)))) with (W64 count) by word.
        replace (Z.of_nat (S count)) with (Z.of_nat count + 1) by lia.
       replace (send_count + 1)%nat with (S send_count) by lia.
       iFrame.
        }
      {
        iFrame. 
      replace ((W64 (uint.Z (W64 count)))) with (W64 count) by word.
        replace (Z.of_nat (S count)) with (Z.of_nat count + 1) by lia.
       replace (send_count + 1)%nat with (S send_count) by lia.
      

     

      (* Now we can frame everything except HQ *)
      iFrame.
      replace (count + 1) with (Z.of_nat (S count)) by lia.
      subst new_xs. subst idx.
      replace ((W64 (uint.Z (W64 params.(ch_size))))) with (W64 params.(ch_size)) by word.
      replace ((W64 (uint.Z (W64 count)))) with (W64 count) by word.
      iFrame. 
      }
      {
        iFrame. 
      replace ((W64 (uint.Z (W64 count)))) with (W64 count) by word.
        replace (Z.of_nat (S count)) with (Z.of_nat count + 1) by lia.
       replace (send_count + 1)%nat with (S send_count) by lia.
      

     

      (* Now we can frame everything except HQ *)
      iFrame.
      replace (count + 1) with (Z.of_nat (S count)) by lia.
      subst new_xs. subst idx.
      replace ((W64 (uint.Z (W64 params.(ch_size))))) with (W64 params.(ch_size)) by word.
      replace ((W64 (uint.Z (W64 count)))) with (W64 count) by word.
      iFrame. 
      }
      {
        iFrame. 
      replace ((W64 (uint.Z (W64 count)))) with (W64 count) by word.
        replace (Z.of_nat (S count)) with (Z.of_nat count + 1) by lia.
       replace (send_count + 1)%nat with (S send_count) by lia.
      

     

      (* Now we can frame everything except HQ *)
      iFrame.
      replace (count + 1) with (Z.of_nat (S count)) by lia.
      subst new_xs. subst idx.
      replace ((W64 (uint.Z (W64 params.(ch_size))))) with (W64 params.(ch_size)) by word.
      replace ((W64 (uint.Z (W64 count)))) with (W64 count) by word.
      iFrame. 
      }
      {
        iFrame. 
      replace ((W64 (uint.Z (W64 count)))) with (W64 count) by word.
        replace (Z.of_nat (S count)) with (Z.of_nat count + 1) by lia.
       replace (send_count + 1)%nat with (S send_count) by lia.
      

     

      (* Now we can frame everything except HQ *)
      iFrame.
      replace (count + 1) with (Z.of_nat (S count)) by lia.
      subst new_xs. subst idx.
      replace ((W64 (uint.Z (W64 params.(ch_size))))) with (W64 params.(ch_size)) by word.
      replace ((W64 (uint.Z (W64 count)))) with (W64 count) by word.
      iFrame. 
      }
        }
      unfold Q.
      replace (params.(ch_size) =? 0) with false by lia.
      destruct params.(ch_is_single_party).
      {

        subst send_count. iFrame. 
        replace (S i) with (i + 1)%nat by lia.
         iFrame.
      }
      {
        unfold Q.
        destruct bool_decide eqn: Hbouter.
        {
          rewrite bool_decide_eq_true in Hbouter.
          destruct bool_decide eqn: Hbinner.
          {
        replace (S i) with (i + 1)%nat by lia.
        iFrame.
          }
          {
            rewrite bool_decide_eq_false in Hbinner.
            lia.
          }
        }
        {
          rewrite bool_decide_eq_false in Hbouter.
          destruct bool_decide.
          {
        replace (S i) with (i + 1)%nat by lia.
            iFrame.
          }
        replace (S i) with (i + 1)%nat by lia.
          iFrame.
        }
      }
  }
 - iModIntro. iApply "HΦ". iFrame "#". iFrame. done.
Qed. 


(* Define word constants for sender results to match Go implementation *)
Definition SENDER_COMPLETED_WITH_RECEIVER_W : w64 := W64 0.
Definition SENDER_MADE_OFFER_W : w64 := W64 1.
Definition SENDER_CANNOT_PROCEED_W : w64 := W64 2.

(* Define result type for better type safety and readability *)
Inductive sender_result := 
  | SenderCompletedWithReceiver
  | SenderMadeOffer
  | SenderCannotProceed.

(* Conversion function from result type to word representation *)
Definition sender_result_to_word (res: sender_result) : w64 := 
  match res with
    | SenderCompletedWithReceiver => SENDER_COMPLETED_WITH_RECEIVER_W
    | SenderMadeOffer => SENDER_MADE_OFFER_W
    | SenderCannotProceed => SENDER_CANNOT_PROCEED_W
  end.

(* Define sender transitions as a simple enum type *)
Inductive sender_transition : Type :=
  | sender_offer_trans
  | sender_complete_trans
  | sender_rescind_trans
  | sender_complete_second_trans.

(* Define a relation that checks if a transition is valid between two states *)
Definition is_valid_send_transition (tr: sender_transition) (vs_old vs_new: valid_chan_state) : Prop :=
  match tr, vs_old, vs_new with
  | sender_offer_trans, Valid_start, Valid_sender_ready => True
  | sender_complete_trans, Valid_receiver_ready, Valid_sender_done => True
  | sender_rescind_trans, Valid_sender_ready, Valid_start => True
  | sender_complete_second_trans, Valid_receiver_done, Valid_start => True
  | _, _, _ => False
  end.

(* Define how sending count changes in each transition *)
Definition sender_send_count_change (tr: sender_transition) : nat :=
  match tr with
  | sender_complete_trans => 1
  | sender_complete_second_trans => 1
  | _ => 0
  end.

(* Define whether additional token is needed for the transition *)
Definition sender_needs_token (tr: sender_transition) : bool :=
  match tr with
  | sender_rescind_trans => true
  | sender_complete_second_trans => true
  | _ => false
  end.

(* Define whether token is produced by the transition *)
Definition sender_produces_token (tr: sender_transition) : bool :=
  match tr with
  | sender_offer_trans => true
  | _ => false
  end.

(* Define whether P resource is needed for the transition *)
Definition sender_needs_P (tr: sender_transition) : bool :=
  match tr with
  | sender_offer_trans => true
  | sender_complete_trans => true
  | _ => false
  end.

(* Define whether Q resource is produced by the transition *)
Definition sender_produces_Q (tr: sender_transition) : bool :=
  match tr with
  | sender_complete_trans => true
  | sender_complete_second_trans => true
  | _ => false
  end.

Lemma sender_transition_general (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V)
  (v vold: V) (vs_old vs_new: valid_chan_state) (tr: sender_transition) 
  (send_count recv_count: nat) (i: nat) (q: Qp):
  is_valid_send_transition tr vs_old vs_new ->
  (if params.(ch_is_single_party) then q = 1%Qp else (q ≤ 1)%Qp) ->

  (* Resources *)
  "HCh" ∷ isUnbufferedChan V params vold vs_old send_count recv_count ∗
  (if sender_needs_token tr then "Hsttok'" ∷ sender_exchange_token params.(ch_γ) v else "Hemp" ∷ emp) ∗ "%Heqv'" ∷  ⌜vold = v ⌝ ∗
  (if sender_needs_P tr then "HP" ∷ P V params.(ch_is_single_party) (Z.of_nat send_count) v params.(ch_Psingle) params.(ch_Pmulti) else emp) ∗
  "HSndCtrAuth" ∷ own_send_counter_auth params.(ch_γ) send_count (send_ctr_frozen vs_old) ∗ 
  "HSndPerm" ∷ own_send_counter_frag params.(ch_γ) i q
  ==∗ 
  (* Result resources *)
  "HCh" ∷ isUnbufferedChan V params vold vs_new 
     (send_count + sender_send_count_change tr) recv_count ∗
  (if negb (sender_produces_Q tr) && negb (sender_needs_P tr) 
  then "HP" ∷ P V params.(ch_is_single_party) (Z.of_nat send_count) v params.(ch_Psingle) params.(ch_Pmulti) else emp ∗
    
  if sender_produces_token tr 
   then "Hsttok" ∷ sender_exchange_token params.(ch_γ) v else emp) ∗ "%Heqv"  ∷ ⌜vold = v ⌝  ∗
  (if sender_produces_Q tr 
   then "HQ" ∷ Q V params.(ch_is_single_party) (Z.of_nat i) params.(ch_Qsingle) params.(ch_Qmulti) else emp) ∗
  "HSndCtrAuth" ∷ own_send_counter_auth params.(ch_γ) (send_count + sender_send_count_change tr) 
                                         (send_ctr_frozen vs_new) ∗ 
  "HSndPerm" ∷ own_send_counter_frag params.(ch_γ) (i + sender_send_count_change tr) q.
Proof.
  intros Hsp Hnn . 
  let x := ident:(Φ) in
  try clear x.
  iIntros "Hpre".
  iNamed "Hpre".
  
  (* First, destruct by transition type to handle each case specifically *)
  destruct tr. all: simpl in *; unfold is_valid_send_transition in Hsp.
  {
  destruct vs_old, vs_new. all: try (exfalso; exact Hsp).
  
  (* Case: sender_offer_trans - Valid_start → Valid_sender_ready *)
    simpl in *.
    
    (* Split unbuffered channel into facts and resources *)
    unfold isUnbufferedChan.
    iDestruct "HCh" as "[%HChanFacts HChanRes]".
    
    (* Extract state resources *)
    iDestruct "HChanRes" as "Hsttok".
    
    (* Handle token splitting *)
  iDestruct ((exchange_token_split params.(ch_γ) true v) with "[$Hsttok]") as ">[Hsttok1 Hsttok2]". iNamed "Hpre".
    
    (* Handle counter verification *)
    iAssert (own_send_counter_auth params.(ch_γ) send_count false ∗ 
             own_send_counter_frag params.(ch_γ) i q ∗ 
             ⌜if params.(ch_is_single_party) then send_count = i else i <= send_count⌝%I)%I
      with "[HSndCtrAuth HSndPerm]" as "(HSndCtrAuth & HSndPerm & %Hispz)".
    {
      destruct params.(ch_is_single_party).
      - replace q with 1%Qp.  
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. done.
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. lia.
    }
    replace (send_count + 0)%nat with (send_count)%nat by lia.
    replace (i + 0)%nat with i by lia.
    
    (* Finalize *)
    iModIntro.
    unfold chan_state_resources.

    
    (* Rebuild resources *)
    iFrame. simpl.  subst v. iFrame. done.
  }
  {
  destruct vs_old, vs_new. all: try (exfalso; exact Hsp).
    
  -  (* Case: sender_complete_trans - Valid_receiver_ready → Valid_sender_done *)
    simpl in *.
    
    (* Split unbuffered channel into facts and resources *)
    unfold isUnbufferedChan. iNamed "Hpre". iNamed "HCh".
    
    (* Extract state resources *)
    
    (* Handle counter verification and update *)
    iAssert (own_send_counter_auth params.(ch_γ) send_count false ∗ 
             own_send_counter_frag params.(ch_γ) i q ∗ 
             ⌜if params.(ch_is_single_party) then send_count = i else i <= send_count⌝%I)%I
      with "[HSndCtrAuth HSndPerm]" as "(HSndCtrAuth & HSndPerm & %Hispz)".
    {
      destruct params.(ch_is_single_party).
      - replace (q) with 1%Qp.
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame.  done.
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame.  iPureIntro. lia.
    }
    
    (* Update counter *)
    iDestruct (send_counter_update params.(ch_γ) send_count i with "[$HSndCtrAuth $HSndPerm]") 
      as ">[HSndCtrAuth HSndPerm]".
    
    (* Finalize *)
    iModIntro.
    (* Rebuild resources *)
    iFrame.
    replace (send_count + 1)%nat with (S send_count)%nat by lia.
    replace (i + 1)%nat with (S i) by lia.
    iFrame. iNamed "HP". iFrame.
    destruct params.(ch_is_single_party).
    {
     subst i. iFrame.
     iFrame. subst v. iFrame. subst send_count. iFrame. done.
    }
    {
      subst v.
      iFrame.
      unfold Q. simpl. subst send_count.  
      destruct (bool_decide (i < 0)%Z) eqn:?; simpl. {iPureIntro. done. }
      destruct recv_count.
      {
       simpl. iFrame. done. 
      }
      simpl. iFrame. done.
    }
  }
  {
  destruct vs_old, vs_new. all: try (exfalso; exact Hsp).

    
   (* Case: sender_rescind_trans - Valid_sender_ready → Valid_start *)
    simpl in *.
    
    (* Split unbuffered channel into facts and resources *)
    unfold isUnbufferedChan.
    iDestruct "HCh" as "[%HChanFacts HChanRes]".
    
    (* Extract state resources *)
    iDestruct "HChanRes" as "(Hsttok & HP')".
    iNamed "Hpre".
    iDestruct "Hpre" as "(H1 & Hrest)". iNamed "Hrest".
  iDestruct ((exchange_token_agree) with "[$Hsttok] [$Hsttok']") as "%Heq".
    
    (* Combine the tokens *)
  iDestruct ((exchange_token_combine) with "[$Hsttok $Hsttok']") as ">Hsttok".
    
    (* Handle counter verification *)
    iAssert (own_send_counter_auth params.(ch_γ) send_count false ∗ 
             own_send_counter_frag params.(ch_γ) i q ∗ 
             ⌜if params.(ch_is_single_party) then send_count = i else i <= send_count⌝%I)%I
      with "[HSndCtrAuth HSndPerm]" as "(HSndCtrAuth & HSndPerm & %Hispz)".
    {
      destruct params.(ch_is_single_party).
      - replace (q) with 1%Qp.
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. done.
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. lia.
    }
    
    (* Finalize *)
    iModIntro.
    
    (* Rebuild resources *)
    replace (send_count + 0)%nat with (send_count)%nat by lia.
    replace (i + 0)%nat with i by lia.
    iFrame.
    unfold chan_state_resources. iFrame.
    destruct Heq as [Heq _].
    rewrite Heqv'.
    iFrame.
    iPureIntro. done.
  }
  {
  destruct vs_old, vs_new. all: try (exfalso; exact Hsp).
    
    
   (* Case: sender_complete_second_trans - Valid_receiver_done → Valid_start *)
    simpl in *.
    
    (* Split unbuffered channel into facts and resources *)
    unfold isUnbufferedChan.
    iDestruct "HCh" as "[%HChanFacts HChanRes]".
    
    (* Extract state resources *)
    iDestruct "HChanRes" as "(Hsttok & HQ)".
    iNamed "Hpre". iDestruct "Hpre" as "(Hemp & Hrest)".
    iNamed "Hrest".
    
    (* Combine the tokens *)
  iDestruct ((exchange_token_agree) with "[$Hsttok] [$Hsttok']") as "%Heq".
  iDestruct ((exchange_token_combine params.(ch_γ)) with "[$Hsttok $Hsttok']") as ">Hsttok".
    
    (* Handle counter verification *)
    iAssert (own_send_counter_auth params.(ch_γ) send_count false ∗ 
             own_send_counter_frag params.(ch_γ) i q ∗ 
             ⌜if params.(ch_is_single_party) then send_count = i else i <= send_count⌝%I)%I
      with "[HSndCtrAuth HSndPerm]" as "(HSndCtrAuth & HSndPerm & %Hispz)".
    {
      destruct params.(ch_is_single_party).
      - replace (q) with 1%Qp.
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. done.
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. lia.
    }

    iDestruct (send_counter_update params.(ch_γ) send_count i with "[$HSndCtrAuth $HSndPerm]") 
      as ">[HSndCtrAuth HSndPerm]".
    
    (* Finalize *)
    iModIntro.
    
    (* Rebuild resources *)
    iFrame .
    
    (* Rebuild channel invariant *)
    iSplitL "".
    {
      iPureIntro. replace (send_count + 1)%nat with (S send_count) by lia.
      done.
    }
    destruct params.(ch_is_single_party).
    {
      subst i. iFrame.
      replace (send_count + 1)%nat with (S send_count) by lia.
    iFrame. destruct Heq as [Heq _]. done.
    }
    {
      unfold Q.
      replace (i + 1)%nat with (S i) by lia.
      replace (send_count + 1)%nat with (S send_count) by lia.
      destruct (bool_decide (i < 0)%Z) eqn:?; simpl.
      {
       iFrame.  
       iPureIntro. destruct Heq as [Heq _]. done.
      }
      iFrame.
       destruct bool_decide.
       {
        word.
       }
       destruct bool_decide eqn:?;simpl.
       {
        apply bool_decide_eq_true in Heqb0.
        lia.
       }
       destruct Heq as [Heq _].
       iFrame.
       done.
    }
  }
Qed.
  
Lemma sender_token_state_agree (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V)
  (v v0: V) (vs: valid_chan_state) (send_count recv_count: nat) :
  vs ≠ Valid_closed →
  sender_exchange_token params.(ch_γ) v -∗
  isUnbufferedChan V params v0 vs send_count recv_count -∗
  ⌜(vs = Valid_sender_ready ∨ vs = Valid_receiver_done) ∧ v = v0⌝.
Proof.
  intros Hvs . 
  iIntros "Htok HChan".
  unfold isUnbufferedChan, chan_state_resources.
  iDestruct "HChan" as "[Hfacts Hres]".

  destruct vs.
  - (* Valid_start *)
    iDestruct "Hres" as "Hfull".
    unfold sender_exchange_token, exchange_token, full_exchange_token.
    iDestruct (ghost_var_valid_2 with "[$Htok] [$Hfull]") as "%Hinvalid".
    destruct Hinvalid as [Hbad _]. apply Qp.not_add_le_r in Hbad. contradiction.

  - (* Valid_receiver_ready *)
    iDestruct "Hres" as "[Hrec HQ]".
    unfold sender_exchange_token, exchange_token, receiver_exchange_token.
    iDestruct "Hrec" as (dummy_v) "Hrec".
    iDestruct (ghost_var_valid_2 with "[$Htok] [$Hrec]") as "%Hbad".
    destruct Hbad as [_ Heq]. inversion Heq.

  - (* Valid_sender_ready *)
    iDestruct "Hres" as "[Htok' HP]".
    iDestruct (ghost_var_agree with "[$Htok] [$Htok']") as "%Heq".
    iPureIntro.  split. { left; reflexivity. }  apply (to_val_inj). set_solver.

  - (* Valid_receiver_done *)
    iDestruct "Hres" as "[Htok' HQ]".
    iDestruct (ghost_var_agree with "[$Htok] [$Htok']") as "%Heq".
    iPureIntro. split; [right; reflexivity | by (apply to_val_inj;set_solver)].

  - (* Valid_sender_done *)
    iDestruct "Hres" as "[Hrec HP]".
    unfold sender_exchange_token, exchange_token, receiver_exchange_token.
    iDestruct "Hrec" as (dummy_v) "Hrec".
    iDestruct (ghost_var_valid_2 with "[$Htok] [$Hrec]") as "%Hbad".
    destruct Hbad as [_ Heq]. inversion Heq.

  - (* Valid_closed *)
    contradiction.
Qed.

Lemma wp_Channel__SenderCheckOfferResult (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V) (i: nat) (q: Qp)
  (vs: valid_chan_state) (send_count recv_count: nat) (v: V):
  params.(ch_loc) ≠ null ->
  (if params.(ch_is_single_party) then q = 1%Qp else (q ≤ 1)%Qp) ->
  (*(#params.(ch_buff).(Slice.sz) = #(W64 0)) -> *)
  vs ≠ Valid_closed ->
  (vs = Valid_receiver_done ∨ vs = Valid_sender_ready) ->
  {{{ 
    is_pkg_init channel ∗
    "value" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "v"] v ∗ 
    "HCh" ∷ isUnbufferedChan V params v vs send_count recv_count ∗ 
    "chan_state" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "state"] (valid_to_word vs) ∗
    "HSndCtrAuth" ∷ own_send_counter_auth params.(ch_γ) send_count (send_ctr_frozen vs) ∗ 
    "Hsttok" ∷ sender_exchange_token params.(ch_γ) v ∗
    "HSndPerm" ∷ own_send_counter_frag params.(ch_γ) i q
  }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "SenderCheckOfferResult" #t #() 
  {{{ (res: rescind_result), RET #(rescind_to_word res);
    match vs, res with
    | Valid_receiver_done, CompletedExchange =>
      "value" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "v"] v ∗ 
      "HCh" ∷ isUnbufferedChan V params v Valid_start (S send_count) recv_count ∗ 
      "chan_state" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "state"] (valid_to_word Valid_start) ∗
      "HSndCtrAuth" ∷ own_send_counter_auth params.(ch_γ) (S send_count) false ∗ 
      "HSndPerm" ∷ own_send_counter_frag params.(ch_γ) (i + 1) q ∗
      "HQ" ∷ Q V params.(ch_is_single_party) (Z.of_nat i) params.(ch_Qsingle) params.(ch_Qmulti)
      
    | Valid_sender_ready, OfferRescinded =>
      "value" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "v"] v ∗ 
      "HCh" ∷ isUnbufferedChan V params v Valid_start send_count recv_count ∗ 
      "chan_state" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "state"] (valid_to_word Valid_start) ∗
      "HSndCtrAuth" ∷ own_send_counter_auth params.(ch_γ) send_count false ∗ 
      "HP" ∷ P V params.(ch_is_single_party) (Z.of_nat send_count) v params.(ch_Psingle) params.(ch_Pmulti) ∗ 
      "HSndPerm" ∷ own_send_counter_frag params.(ch_γ) i q
      
    | _, _ =>
      False
    end
  }}}.
Proof.
  intros  Hnn Hsp Hbuffsz Hnot_closed.
  let x := ident:(Φ) in
  try clear x.
  iIntros (Φ) "Hpre HΦ".
  destruct_pkg_init "Hpre".
  try (first [ wp_func_call | wp_method_call ]; wp_call; [idtac]).
  wp_auto_lc 1. iDestruct "Hpre" as "[Hpre Hmu]". iNamed "Hpre". 
  rewrite -wp_fupd.
  iNamed "Hmu". unfold isUnbufferedChan.
  iDestruct "HCh" as "[H1 H2]".
  unfold chan_state_resources.
  destruct vs.
  
  - (* Valid_start case: Not a valid state *)
    destruct Hnot_closed as [Hvs | Hvs]; discriminate.
    
  - (* Valid_receiver_ready case: Not a valid state *)
    destruct Hnot_closed as [Hvs | Hvs]; discriminate.
  -
   (* Valid_sender_ready case: Can rescind offer *)
  destruct Hnot_closed as [Hvs | Hvs]; try discriminate.
  wp_auto.
  unfold isUnbufferedChan.
  unfold chan_state_resources.
  iNamed "H1". iNamed "H2".
  
  (* Apply sender_transition_general *)
  iMod (sender_transition_general V params v v Valid_sender_ready Valid_start 
       sender_rescind_trans send_count recv_count i with 
      "[ HP HSndPerm HSndCtrAuth Hextok Hsttok]") as 
      "IH".
  { (* Prove valid transition *)
    unfold is_valid_send_transition.
    destruct Valid_sender_ready, Valid_start; try done.
  }
  { (* Ownership constraint *)
    exact Hsp.
  }
  {
    simpl.
    iFrame. done.
  }
  
  
  (* Finalize *)
  iModIntro.
  iSpecialize ("HΦ" $! OfferRescinded).
  
  iApply "HΦ". iNamed "IH". simpl. iNamed "IH". 
  iFrame. simpl. iNamed "HCh". iDestruct "IH" as "[H1 H2]".
  replace (send_count + 0)%nat with send_count by lia.
  replace (i + 0)%nat with i by lia.
  iFrame. iPureIntro. lia.
  
- (* Valid_receiver_done case: Can complete exchange *)
  destruct Hnot_closed as [Hvs | Hvs]; try discriminate.
  wp_auto. iNamed "H2". iNamed "H1".
  
  iMod (sender_transition_general V params v v Valid_receiver_done Valid_start 
       sender_complete_second_trans send_count recv_count i with 
      "[HQ Hextok  HSndCtrAuth HSndPerm Hsttok]") as 
      "IH".

  { (* Prove valid transition *)
    unfold is_valid_send_transition.
    destruct Valid_receiver_done, Valid_start; try done.
  }
  { (* Ownership constraint *)
    exact Hsp.
  }
  { 
    iFrame.
    (* Need to supply HP if needed *)
    destruct (sender_needs_P sender_complete_second_trans).
    + simpl. unfold isUnbufferedChan. simpl. unfold chan_state_resources.
    iFrame. done.
    + simpl. unfold isUnbufferedChan. simpl. unfold chan_state_resources.
     iFrame. done.
  }
  
  (* Finalize *)
  iModIntro.
  iSpecialize ("HΦ" $! CompletedExchange).
  iApply "HΦ". 
  iFrame. simpl.  
  replace (send_count + 0)%nat with send_count by lia.
  replace (send_count + 1)%nat with (S send_count) by lia.
  replace (i + 0)%nat with i by lia.
  iNamed "IH". iDestruct "IH" as "[He Hrest]".
  iNamed "Hrest".
  iFrame. 
  
- (* Valid_sender_done case: Not a valid state *)
  destruct Hnot_closed as [Hvs | Hvs]; discriminate.
  
- (* Valid_closed case *)
  exfalso. done.
Qed.

Lemma wp_Channel__SenderCompleteOrOffer (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V) (i: nat) (q: Qp) (v vold: V)
  (vs: valid_chan_state) (send_count recv_count: nat):
  params.(ch_loc) ≠ null ->
  (if params.(ch_is_single_party) then q = 1%Qp else (q ≤ 1)%Qp) ->
  vs ≠ Valid_closed ->
  {{{ 
    is_pkg_init channel ∗
    "value" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "v"] vold ∗ 
    "HCh" ∷ isUnbufferedChan V params vold vs send_count recv_count ∗ 
    "chan_state" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "state"] (valid_to_word vs) ∗
    "HP" ∷ P V params.(ch_is_single_party) (Z.of_nat i) v params.(ch_Psingle) params.(ch_Pmulti) ∗
    "HSndCtrAuth" ∷ own_send_counter_auth params.(ch_γ) send_count (send_ctr_frozen vs) ∗ 
    "HSndPerm" ∷ own_send_counter_frag params.(ch_γ) i q
  }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "SenderCompleteOrOffer" #t #v
  {{{ (res: sender_result), RET #(sender_result_to_word res);
    match res, vs with
    | SenderCompletedWithReceiver, Valid_receiver_ready =>
      "value" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "v"] v ∗ 
      "HCh" ∷ isUnbufferedChan V params v Valid_sender_done (send_count + 1) recv_count ∗ 
      "chan_state" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "state"] (valid_to_word Valid_sender_done) ∗
      "HSndCtrAuth" ∷ own_send_counter_auth params.(ch_γ) (send_count + 1) false ∗ 
      "HSndPerm" ∷ own_send_counter_frag params.(ch_γ) (i + 1) q ∗
      "HQ" ∷ Q V params.(ch_is_single_party) (Z.of_nat i) params.(ch_Qsingle) params.(ch_Qmulti)
      
    | SenderMadeOffer, Valid_start =>
      "value" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "v"] v ∗ 
      "HCh" ∷ isUnbufferedChan V params v Valid_sender_ready send_count recv_count ∗ 
      "chan_state" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "state"] (valid_to_word Valid_sender_ready) ∗
      "HSndCtrAuth" ∷ own_send_counter_auth params.(ch_γ) send_count false ∗ 
      "HSndPerm" ∷ own_send_counter_frag params.(ch_γ) i q ∗
      "Hsttok" ∷ sender_exchange_token params.(ch_γ) v
      
    | SenderCannotProceed, _ =>
      "value" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "v"] vold ∗ 
      "HCh" ∷ isUnbufferedChan V params vold vs send_count recv_count ∗ 
      "chan_state" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "state"] (valid_to_word vs) ∗
      "HP" ∷ P V params.(ch_is_single_party) (Z.of_nat i) v params.(ch_Psingle) params.(ch_Pmulti) ∗
      "HSndCtrAuth" ∷ own_send_counter_auth params.(ch_γ) send_count (send_ctr_frozen vs) ∗ 
      "HSndPerm" ∷ own_send_counter_frag params.(ch_γ) i q
      
    | _, _ => False
    end
  }}}.
Proof.
  intros Hnn Hsp Hvs Hnot_closed.
  let x := ident:(Φ) in
  try clear x.
  iIntros "Hpre HΦ".
  destruct_pkg_init "Hpre".
  try (first [ wp_func_call | wp_method_call ]; wp_call; [idtac]).
  wp_auto_lc 1. iDestruct "Hpre" as "[Hpre Hmu]". iNamed "Hpre". 
  rewrite -wp_fupd.
  (* Cases based on vs ≠ Valid_closed *)
  iNamed "Hmu". 
  destruct vs.
  
  - (* Valid_start case: Can make an offer *)
    wp_auto.
    (* Handle counter verification and update *)
    iAssert (own_send_counter_auth params.(ch_γ) send_count false ∗ 
             own_send_counter_frag params.(ch_γ) i q ∗ 
             ⌜if params.(ch_is_single_party) then send_count = i else i <= send_count⌝%I)%I
      with "[HSndCtrAuth HSndPerm]" as "(HSndCtrAuth & HSndPerm & %Hispz)".
    {
      destruct params.(ch_is_single_party).
      - replace (q) with 1%Qp.
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. done.
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. lia.
    }
    iMod (sender_transition_general V params v v Valid_start Valid_sender_ready 
       sender_offer_trans send_count recv_count i with 
      "[HCh HSndCtrAuth HSndPerm HP]") as 
      "IH".

    { (* Prove valid transition *)
      unfold is_valid_send_transition.
      destruct Valid_start, Valid_sender_ready; try done.
    }
    { (* Ownership constraint *)
      exact Hsp.
    }
    { 
      simpl.
      unfold isUnbufferedChan. unfold chan_state_resources.
      iFrame.
      unfold P.
      destruct params.(ch_is_single_party).
      {
        subst. iFrame.
        done.
        }
        (* Supply HP for this transition *)
        iFrame.
        done.
    }
    
    (* Finalize *)
    iModIntro.
    iSpecialize ("HΦ" $! SenderMadeOffer).
    iApply "HΦ". simpl.
    replace (send_count + 0)%nat with send_count by lia.
    replace (i + 0)%nat with i by lia.
    iNamed "IH". iDestruct "IH" as "[Hemp Hrest]".
    iDestruct "Hemp" as "[H1 H2]".
    iFrame. iNamed "Hrest". iFrame. iNamed "HCh".
    iFrame. iDestruct "Hrest" as "(Hemp & H2 & H3)".
    iFrame. iPureIntro. done.
    
  - (* Valid_receiver_ready case: Can complete exchange *)
    wp_auto.
    iAssert (own_send_counter_auth params.(ch_γ) send_count false ∗ 
             own_send_counter_frag params.(ch_γ) i q ∗ 
             ⌜if params.(ch_is_single_party) then send_count = i else i <= send_count⌝%I)%I
      with "[HSndCtrAuth HSndPerm]" as "(HSndCtrAuth & HSndPerm & %Hispz)".
    {
      destruct params.(ch_is_single_party).
      - replace q with 1%Qp.
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. done.
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. lia.
    }
    
    (* Apply transition using the general lemma *)
    unfold isUnbufferedChan. unfold chan_state_resources.
    iMod (sender_transition_general V params v v Valid_receiver_ready Valid_sender_done 
       sender_complete_trans send_count recv_count i with 
      "[HCh HSndCtrAuth HSndPerm HP]") as 
      "IH".
    { (* Prove valid transition *)
      unfold is_valid_send_transition.
      destruct Valid_receiver_ready, Valid_sender_done; try done.
    }
    { (* Ownership constraint *)
      exact Hsp.
    }
    { 
      iFrame.
      simpl.
      unfold P.
      destruct params.(ch_is_single_party).
      {
        subst. iFrame. done.

      }
      (* Supply HP for this transition *)
      iFrame.
     done. 
    }
    
    (* Finalize *)
    iModIntro.
    simpl.
    iNamed "IH". iDestruct "IH" as "[Hemp IH]".
    iNamed "IH".
    iSpecialize ("HΦ" $! SenderCompletedWithReceiver).
    iApply "HΦ". 
    iFrame. 
    
  - (* Valid_sender_ready case: Cannot proceed *)
    wp_auto.
    iSpecialize ("HΦ" $! SenderCannotProceed).
    iApply "HΦ". 
    iFrame. iModIntro. done.
    
  - (* Valid_receiver_done case: Cannot proceed *)
    wp_auto.
    iSpecialize ("HΦ" $! SenderCannotProceed).

    iApply "HΦ". 
    iFrame. iModIntro. done.
    
  - (* Valid_sender_done case: Cannot proceed *)
    wp_auto.
    iSpecialize ("HΦ" $! SenderCannotProceed).
    iApply "HΦ". 
    iFrame. iModIntro. done.
    
  - (* Valid_closed case *)
    exfalso. done.
Qed.

  Lemma wp_Channel__TrySend (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V) (i: nat) (q: Qp) (v: V):
  (* Could let bindings be implicit args? *)
    0 ≤ params.(ch_size) ->
    params.(ch_size) + 1 < 2 ^ 63 ->
    
    (if params.(ch_is_single_party) then q = 1%Qp else (q ≤ 1)%Qp) ->
    {{{ is_pkg_init channel ∗ send_pre V params q i v }}}
      params.(ch_loc) @ channel @ "Channel'ptr" @ "TrySend" #t #v
{{{ (selected: bool), RET #selected; 
        if (selected) then 
        send_post V params q i else 
        send_pre V params q i v
    }}}.
  Proof. 
  intros  Hszgt Hszlt Hsp. wp_start. wp_auto.  
  iNamed "Hpre". iNamed "HCh". wp_auto. 
  iDestruct (chan_pointsto_non_null V (params.(ch_mu)) params with "mu") as %HNonNull.
  assert (params .(ch_loc) ≠ null).
  {
    intro H1.
    rewrite H1 in HNonNull. done.
  }
  wp_if_destruct.
  - (* Case: Unbuffered channel (size = 0) *)
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked HisChanInner]". wp_auto.
  iNamed "HisChanInner".
  
  (* Verify that the channel is not closed *)
  iAssert (⌜ vs ≠ Valid_closed ⌝%I ) as "%Hnot_closed".
  {
   
     destruct vs; try done.
    (* Proof by contradiction - if closed, we get an ownership conflict *)
    iDestruct "HCloseTokPostClose" as (n close_tok_names) "[HCloseTokPost HSendCtrFrag]".
    iCombine "HSendCtrFrag" "HSc" as "H" gives "%Hvalid". 
   apply auth_frag_op_valid_1 in Hvalid.
             rewrite <- (Some_op (1%Qp, n) (q, i)) in Hvalid.
             rewrite Some_valid in Hvalid.
             rewrite <- (pair_op 1%Qp q n i) in Hvalid.
             rewrite pair_valid in Hvalid. destruct Hvalid as [Hqvalid Hivalid].
             rewrite frac_op in Hqvalid.

             assert (((1 + q)%Qp ≤ 1)%Qp).
             { 
              done. 
             }
             apply Qp.not_add_le_l in H0.
             contradiction.
  }
  

    assert (params.(ch_size) = 0) as Hl.
    {  
      assert (W64 0 = W64 params.(ch_size)).
{ 
  apply (inj _) in Hbuffsize.
  word.
} replace (params.(ch_size)) with (uint.Z (W64 params.(ch_size))).
{
 replace (W64 params.(ch_size)) with (W64 0). done. 
}  
word. }
assert ((params.(ch_size) =? 0) = true) by lia.
  (* Apply SenderCompleteOrOffer *)
  iDestruct "HChanState" as "HUnbuffCh".
wp_apply (wp_Channel__SenderCompleteOrOffer V params i q v v0 vs
          send_count recv_count with "[value HUnbuffCh state  HP HSndCtrAuth HSc]").
  all: try done.

  {  (* Frame resources *) iFrame. simpl. 
  simpl. iFrame. rewrite H0. iFrame.
  }
  
  iIntros (res) "Hres".
  
 wp_auto. 
  
  (* Branch based on sender result *)
  destruct res, vs. all:try done.
  
  
  + (* SenderCompletedWithReceiver, Valid_receiver_ready *)
    iNamed "Hres".
    
    (* Release mutex *)
    wp_apply (wp_Mutex__Unlock with "[$Hlock value chan_state first count HSndCtrAuth HRcvCtrAuth 
     HCloseTokPostClose HCh $Hlocked]").
    {
      iModIntro. unfold isChanInner. 
      iExists Valid_sender_done, count, first, v, (S send_count), recv_count.
      iFrame.   iFrame. replace (send_count + 1)%nat with (S send_count) by lia.
      rewrite H0. iFrame.
    }
    
    (* Return success *)
    
    iApply "HΦ". simpl. iFrame.  simpl. rewrite Hl.  simpl. iFrame.  replace (i - 0%nat) with (Z.of_nat i) by lia.
     replace (i -0) with (Z.of_nat i) by lia. iFrame.

  
  (* SenderMadeOffer, Valid_start - check offer result *)
  + iNamed "Hres".
    
    (* Release mutex *)
    wp_apply (wp_Mutex__Unlock with "[$Hlock value count first chan_state HSndCtrAuth HRcvCtrAuth 
     HCloseTokPostClose HCh $Hlocked]").
    {
      iModIntro. 
      iExists Valid_sender_ready, count, first, v, send_count, recv_count.
      iFrame. rewrite Hl.    iFrame.
    }
    
    (* Check offer result *)
    wp_apply (wp_Mutex__Lock with "[$Hlock]").
    iIntros "[locked inv]". wp_auto.

    iNamed "inv". 
    destruct (decide (vs =?= Valid_closed)) as [Heq|Hneq].
{
replace vs with Valid_closed.
{
 iNamed "HCloseTokPostClose". iDestruct "HCloseTokPostClose" as "[Hct1 Hct2]".
 iDestruct (own_valid_2 with "[$Hct2] [$HSndPerm]") as "%Hvalid". 
 apply auth_frag_op_valid_1 in Hvalid.
rewrite <- (Some_op (1%Qp, n) (q, i)) in Hvalid.
rewrite Some_valid in Hvalid.
rewrite <- (pair_op 1%Qp q n i) in Hvalid.
rewrite pair_valid in Hvalid. destruct Hvalid as [Hqvalid _].
rewrite frac_op in Hqvalid.
assert (((1 + q)%Qp ≤ 1)%Qp) by done.
apply Qp.not_add_le_l in H1.
contradiction.
}
{
  destruct vs. all: done.
}
}


    
    iDestruct (( sender_token_state_agree V params v v1 vs send_count0 recv_count0  ) with " [Hsttok] [HChanState]") as "%Hct".
    {
       destruct vs. all: done.
    }
    {
     iFrame. 
    }
    {
     iFrame. rewrite Hl. iFrame.
    }
    destruct Hct as [Hvsr Hvv0].
    subst v1.
    
    
    unfold isUnbufferedChan. unfold chan_state_resources.
      iAssert (own_send_counter_auth params.(ch_γ) send_count0 (send_ctr_frozen vs) ∗ 
              own_send_counter_frag params.(ch_γ) i q ∗ 
              ⌜if params.(ch_is_single_party) then send_count0 = i else i <= send_count0⌝%I)%I
        with "[HSndCtrAuth HSndPerm]" as "(HSndCtrAuth & HSen & %Hispz)".
      {
        destruct params.(ch_is_single_party).
        - replace q with 1%Qp.
          iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
          iFrame. iPureIntro. lia.  
        - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
          iFrame. iPureIntro. lia. 
      }
      iAssert (isUnbufferedChan V params v vs send_count0 recv_count0) with "[HChanState]" as "HCh".
{
  unfold isUnbufferedChan. rewrite Hl.
  iFrame "HChanState".
}
 simpl.  
wp_apply (wp_Channel__SenderCheckOfferResult V params i q vs send_count0 recv_count0 v  
          with "[$HSndCtrAuth $HCh $state $value $Hsttok $HSen]").
   
            all: (try done;try word; try lia; try iFrame).
  { 
    destruct vs. all: done.
  }
  {
    inversion Hvsr.
    {
     right. done. 
    }
    left. done.
  }
  iIntros (res) "Hvs". destruct res.
  {
   simpl. wp_auto.  
   destruct vs. all: try done. iNamed "Hvs". iNamed "HCh".
   wp_apply (wp_Mutex__Unlock with "[$Hlock HRcvCtrAuth count first  HSndCtrAuth value chan_state 
      HCh  $locked]").
      {
      iModIntro. iExists Valid_start. iFrame. unfold isChanInner. iFrame "#". 
      simpl. iFrame. rewrite Hl. simpl. iFrame.
      iPureIntro. done.
    }
    iApply "HΦ". iFrame.
    unfold P. destruct params.(ch_is_single_party).
    {
      subst send_count0.
     iFrame "#". iFrame.  iFrame "#". rewrite Hl. iFrame. iPureIntro. rewrite e.
     done.
 }
    unfold P. iFrame "#". iFrame. iPureIntro. done.
   
  }
  {
    simpl. wp_auto.  
    destruct vs. all: try done. iNamed "Hvs".
    wp_apply (wp_Mutex__Unlock with "[$Hlock HRcvCtrAuth count first  HSndCtrAuth value chan_state 
       HCh $locked]").
     {
       iModIntro. iExists Valid_start. iFrame. 
     simpl. iFrame. rewrite Hl. iFrame. done.
     }
     iApply "HΦ". iFrame.
     unfold P. destruct params.(ch_is_single_party).
     {
       subst send_count0.
      iFrame. rewrite Hl.  replace (i - 0) with (Z.of_nat i) by lia. iFrame. 
     }
      iFrame.
     rewrite Hl.  replace (i - 0) with (Z.of_nat i) by lia. iFrame. 

  }
  { wp_auto.  
    destruct vs. all: try done. 
  }
  + iNamed "Hres".
  
  wp_apply (wp_Mutex__Unlock with "[$Hlock HRcvCtrAuth count first  HSndCtrAuth value chan_state 
  HCh $Hlocked]").
{
  iModIntro. iFrame. rewrite Hl. iFrame. done.  
}
{
 iApply "HΦ". iFrame. iFrame "#". iPureIntro. done.
}
  + iNamed "Hres".
  
  wp_apply (wp_Mutex__Unlock with "[$Hlock HRcvCtrAuth count first  HSndCtrAuth value chan_state 
  HCh $Hlocked]").
{
  iModIntro. iFrame. rewrite Hl. simpl.  iFrame. done.  
}
{
 iApply "HΦ". iFrame "#". iFrame. iPureIntro. done.
}
+ iNamed "Hres".
  
wp_apply (wp_Mutex__Unlock with "[$Hlock HRcvCtrAuth count first  HSndCtrAuth value chan_state 
HCh $Hlocked]").
{
iModIntro. iFrame. rewrite Hl. simpl. iFrame. done.  
}
{
iApply "HΦ". iFrame. iFrame "#". iPureIntro. done.
}
+ iNamed "Hres".

wp_apply (wp_Mutex__Unlock with "[$Hlock HRcvCtrAuth count first  HSndCtrAuth value chan_state 
HCh $Hlocked]").
{
iModIntro. iFrame.  iFrame. simpl. rewrite Hl. iFrame. done. 
}
{
iApply "HΦ". iFrame "#". iFrame.
iPureIntro. done.
}
+ iNamed "Hres".
  
wp_apply (wp_Mutex__Unlock with "[$Hlock HRcvCtrAuth count first  HSndCtrAuth value chan_state 
HCh $Hlocked]").
{
iModIntro. iFrame. rewrite Hl. iFrame. done.
}

{
iApply "HΦ". iFrame. iFrame "#".
iPureIntro. done. 
}
  - (* Case: Buffered channel (size > 0) *)
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[locked Hinv]".
  iNamed "Hinv".
    
    (* Verify that the channel is not closed *)
    iAssert (⌜ vs ≠ Valid_closed ⌝%I ) as "%Hnot_closed".
    {
     
       destruct vs; try done.
       iNamed "HCloseTokPostClose".
       iDestruct "HCloseTokPostClose" as "[Hcp Hsc']".
      (* Proof by contradiction - if closed, we get an ownership conflict *)
      iCombine "Hsc'" "HSc"  as "H" gives "%Hvalid". 
      simpl in Hvalid.
     apply auth_frag_op_valid_1 in Hvalid.
               rewrite <- (Some_op (1%Qp, n0) (q, i)) in Hvalid.
               rewrite Some_valid in Hvalid.
               rewrite <- (pair_op 1%Qp q n0 i) in Hvalid.
               rewrite pair_valid in Hvalid. destruct Hvalid as [Hqvalid Hivalid].
               rewrite frac_op in Hqvalid.

               assert (((1 + q)%Qp ≤ 1)%Qp).
               { 
                done. 
               }
               apply Qp.not_add_le_l in H0.
               contradiction.
    }
    
    (* Identify channel state as buffered *)
    assert (params.(ch_size) > 0) as Hsize_pos.
    {
      assert ((params .(ch_buff) .(slice.len_f)) = (W64 params .(ch_size))).
      {
       apply (inj _) in Hbuffsize.
       done.
      }

      destruct params.(ch_size). { word. }
      { done. }
      done.
    }
    assert ((params.(ch_size) =? 0) = false) by lia.
    rewrite H0. iNamed "HChanState". unfold isBufferedChan.
    unfold isBufferedChanLogical.

    wp_apply (wp_Channel__BufferedTrySend_params V params q i v with 
          "[HP HSc HSndCtrAuth HCloseTokPostClose HRcvCtrAuth state value count HPs HQs HBuffSlice first]"). 
          all: try done.
          { 
iFrame "∗#".  rewrite H0. iFrame. 

  unfold send_ctr_frozen. 
        destruct vs. all: try (iFrame;iPureIntro;set_solver).
          }
        {
        
        iIntros (success) "IH". 
        destruct success.
        {
          
         iNamed "IH". wp_auto. iNamed "IH". iNamed "HCh".
         wp_apply (wp_Mutex__Unlock with
          "[$Hlock state count HCloseTokPostClose HChanState first value HRcvCtrAuth HSndCtrAuth $locked]")
          .
        { iModIntro. unfold isChanInner. iExists vs0, count0, first0, v1, send_count0, recv_count0. unfold send_ctr_frozen. rewrite H0. iFrame. 
        }
        iApply "HΦ". iFrame.
        }
        {
          iDestruct "buffer" as "_". iNamed "IH".
          iNamed "HCh". 
          iAssert(⌜ vs0 ≠ Valid_closed ⌝%I) as "%Hvc".
          {
          destruct (decide (vs0 =?= Valid_closed)) as [Heq|Hneq].
          {
          replace vs0 with Valid_closed.
          {
           iNamed "HCloseTokPostClose". iDestruct "HCloseTokPostClose" as "[Hct1 Hct2]".
           iDestruct (own_valid_2 with "[$Hct2] [$HSc]") as "%Hvalid". 
           apply auth_frag_op_valid_1 in Hvalid.
          rewrite <- (Some_op (1%Qp, n0) (q, i)) in Hvalid.
          rewrite Some_valid in Hvalid.
          rewrite <- (pair_op 1%Qp q n0 i) in Hvalid.
          rewrite pair_valid in Hvalid. destruct Hvalid as [Hqvalid _].
          rewrite frac_op in Hqvalid.
          assert (((1 + q)%Qp ≤ 1)%Qp) by done.
          apply Qp.not_add_le_l in H1.
          contradiction.
          }
          {
            destruct vs0. all: done.
          }
          }
        iAssert (own_send_counter_auth params.(ch_γ) send_count0 false ∗ 
                own_send_counter_frag params.(ch_γ) i q ∗ 
                ⌜if params.(ch_is_single_party) then send_count0 = i else i <= send_count0⌝%I)%I
          with "[HSndCtrAuth HSc]" as "(HSndCtrAuth & HSen & %Hispz)".
        {
          destruct params.(ch_is_single_party).
          - replace (q) with 1%Qp.
            iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSc]") as "%Hag2".
          subst send_count0.
             unfold send_ctr_frozen. destruct vs0. all: try (iFrame;iPureIntro;set_solver). set_solver.
             
          - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSc]") as "%Hag2".
            iFrame. unfold send_ctr_frozen. destruct vs0. all: try done;(iFrame;iPureIntro;try done;lia). 

        }
           iPureIntro. set_solver.
          }
         wp_auto.
         wp_apply (wp_Mutex__Unlock with
          "[$Hlock state count first value HRcvCtrAuth HSndCtrAuth HChanState $locked]").
          { 
            iModIntro. unfold isChanInner. iFrame.
            destruct vs0. all:try iFrame;done.
          }
            
       iApply "HΦ". iFrame.
       replace (i + 1)%nat with (S i) by lia.
       iFrame. iFrame "#". iPureIntro. done.

        }
        }

Qed.


Lemma wp_Channel__TryClose (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V)
       (n : nat) :
  {{{ is_pkg_init channel ∗  
  
  "HCh" ∷ isChanInner V params  ∗
  "HCp" ∷   own_close_perm params.(ch_γ) params.(ch_R) n }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "TryClose" #t #()
  {{{ (selected : bool), RET #selected;
      (if selected then
        
           isChanInnerClosed V params 

       else
       own_close_perm params.(ch_γ) params.(ch_R) n
       ∗ 
           isChanInner V params 
       ) 
      
  }}}.
   wp_start. wp_auto_lc 1. 
  iNamed "Hpre". iNamed "HCh". wp_auto.
    rewrite -wp_fupd.
  wp_if_destruct.
  {
    assert (vs = Valid_closed).
    {
     destruct vs. all: done. 
    }
    subst vs. iNamed "HCloseTokPostClose".
    iDestruct "HCloseTokPostClose" as  "[HCloseTokPost HSendCtrFrag]".
    unfold own_close_perm.
    iDestruct "HCp" as "(HR & HSc & Hct)".
    iCombine "HSendCtrFrag" "HSc" as "H" gives "%Hvalid". 
   apply auth_frag_op_valid_1 in Hvalid.
             rewrite <- (Some_op (1%Qp, n0) (1%Qp, n)) in Hvalid.
             rewrite Some_valid in Hvalid.
             rewrite <- (pair_op 1%Qp 1%Qp n0 n) in Hvalid.
             rewrite pair_valid in Hvalid. destruct Hvalid as [Hqvalid Hivalid].
             rewrite frac_op in Hqvalid.

             assert (((1 + 1)%Qp ≤ 1)%Qp).
             { 
              done. 
             }
             apply Qp.not_add_le_l in H.
             contradiction.
  }
  wp_auto.
  wp_if_destruct.
  {
   iApply "HΦ". iFrame "#".  iFrame. 
   iModIntro. done.
  }
  wp_auto.
  wp_if_destruct.
  {
   iApply "HΦ". iFrame "#". iFrame. 
   iModIntro. done.
  }
  unfold own_close_perm. unfold own_closed_tok_auth.
  iDestruct "HCp" as "(HR & Hsc & Hn)".
  iNamed "Hn".
  
  wp_auto_lc 1. iApply "HΦ". iFrame.  unfold own_close_perm.
  iApply "Hn" in "HR".
  iDestruct ((lc_fupd_elim_later _ ([∗ set] γi ∈ close_tok_names, ∃ Ri : nat → iProp Σ,
  saved_prop.saved_pred_own γi DfracDiscarded
  Ri ∗ Ri n)) with "[$] [HR]") as "HRelimlater".
  {
    iModIntro. iFrame.
  }

   

  iFrame.
  iExists send_count. iExists recv_count.
  iFrame. iSplitL "HSndCtrAuth".
  {
    simpl.
 iDestruct ((send_counter_freeze params.(ch_γ) send_count) with "[$]") as ">HSc".
 iModIntro. done.
  }
  iSplitL "HRcvCtrAuth".
  {
    simpl.
 destruct (send_count =? recv_count).
 {
 iDestruct ((recv_counter_freeze params.(ch_γ) recv_count) with "[$]") as ">HSc".
 iModIntro. iFrame.
 }
 {
  unfold recv_ctr_frozen.
  iModIntro.
  destruct vs. all: try (iFrame;done).
 }
  }
  unfold own_closed_tok_post_close.
  unfold own_closed_tok_auth.
  destruct (params .(ch_size) =? 0).
  { 
    unfold isUnbufferedChan.
    iDestruct "HChanState" as "[H1 H2]".
    unfold chan_state_facts.
    iDestruct "HRelimlater" as ">HR".
    iModIntro.
    destruct vs. all: try done;try iFrame.
  }
  {
   iFrame. 
    iDestruct "HRelimlater" as ">HR".
   iModIntro. done.
  }
Qed.

End proof.

