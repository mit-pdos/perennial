From Perennial.goose_lang Require Import prelude. 
From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode array.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang.automation Require Import extra_tactics.
From Perennial.goose_lang.lib Require Import
      persistent_readonly slice slice.typed_slice struct loop lock control map.typed_map time proph rand string typed_mem.

From Perennial.goose_lang.lib.channel Require Import auth_set.
From Perennial.goose_lang.lib.channel Require Import chan_use_ctr.
From Perennial.goose_lang.lib.channel Require Import chan_spec_multi_base.
From Goose.github_com.goose_lang.goose Require Import channel.
From Perennial.goose_lang Require Import lang typing.


Section proof.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}. 
Context `{!closePropTrackerG Σ, !inG Σ (authR (optionUR (prodR fracR natR)))}.
Context `{!ghost_varG Σ (bool * val)}.

Implicit Types (v:val).

Notation "vs1 =?= vs2" := (valid_chan_state_eq vs1 vs2) (at level 70).
    
Lemma wp_Channel__TryReceive (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) 
(Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat -> iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
{{{ 
  "HCh" ∷ isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
}}}
Channel__TryReceive chan_type #ch
{{{ (v: val) (ok: bool) (selected: bool), RET (#selected,v,#ok); 
  if selected then 
    (if ok then 
      ((P is_single_party i v Psingle Pmulti ∗ own_recv_perm γ q (i + 1) Ri ∗ ⌜ok⌝ ∗ ⌜val_ty v chan_type⌝))
    else
      (own_recv_counter_frag γ i q ∗ ⌜v = (zero_val chan_type)⌝ ∗ ⌜ok = false⌝
       ∗ ∃ n, (Ri n) ∗ own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true))
  else 
    (Q is_single_party i Qsingle Qmulti ∗ own_recv_perm γ q i Ri)
}}}.
Proof.
  intros Hsp.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  
  wp_rec. wp_pures.
  
  (* Decide if channel is buffered or unbuffered *)
  iNamed "HCh".
  wp_loadField.
  wp_apply wp_slice_len.

  wp_if_destruct.

  
  (* Case: Buffered channel (size > 0) *)
  - 
    assert (size > 0)%nat as Hsize_pos by word.
    (* Handle buffered case based on count and channel state *)
    assert ((size =? 0) = false) by lia.
  
  (* Call BufferedTryReceive *)
    wp_rec.
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked HisChanInner]". wp_pures.
    unfold isChanInner. iNamed "HisChanInner".
   (* destruct (vs =?= Valid_closed) eqn: Hc.
    {
      assert (vs = Valid_closed).
      { destruct vs. all: done. }
      replace vs with Valid_closed.
      subst vs. rewrite H. iNamed "HisChanInner".
    } *)
    
    (* Extract inner channel details *)
    iNamed "HisChanInner".
    
    (* Assert that size > 0 *)
    rewrite H. iNamed "HisChanInner".
    destruct (uint.Z (W64 0) <? uint.Z (W64 count)) eqn: Hb.
    {
    + (* Case: Buffered channel (size > 0) with data available *)
      wp_apply (wp_Channel__BufferedTryReceiveLocked ch γ chan_type size mu_l is_single_party vs
               count send_count recv_count first buff
               Psingle Pmulti Qsingle Qmulti R Ri i q
               with "[buff count chan_state HChanState first HRecvPerm HQ HRcvCtrAuth]").
      *  done.
      * done.
      * rewrite Hb. iFrame. iFrame "#".
      * iIntros (success). iIntros (v0). iIntros (has_value). iIntros "Hres".
        wp_loadField. 
       
        wp_pures.
        
        (* Unlock mutex *)
        destruct success eqn: Hqs, has_value eqn: Hqb.
        { iNamed "Hres". iNamed "Hres".
        wp_apply (wp_Mutex__Unlock with "[$Hlock HCh HRecvCtrAuth first count chan_state value HSndCtrAuth HCloseTokPostClose  $Hlocked]").
        {
            iModIntro.
            unfold isChanInner. 
            iExists vs, (count - 1)%nat, new_first, v, send_count, (S recv_count).
            iFrame. replace (W64 (count - 1)%nat) with (W64 (count-1)) by word.
            iFrame.    replace (Z.of_nat count - 1) with (Z.of_nat (count-1)) by word. iFrame.
        }
        {
         wp_pures. iModIntro. iApply "HΦ". iFrame. replace (i + 1)%nat with (S i) by lia. iFrame. done.
        }
        }
        {
          iNamed "Hres".
          iNamed "Hres". iDestruct "Hres" as "[%Hvs %Hvz]". subst vs.
          iNamed "HCloseTokPostClose". iDestruct "HCloseTokPostClose" as "[Hct1 Hct2]".
          iDestruct (own_valid_2 with "[$Hct2] [$HSc]") as "%Hvalid". 
          apply auth_frag_op_valid_1 in Hvalid.
          rewrite <- (Some_op (1%Qp, n) (1%Qp, recv_count)) in Hvalid.
          rewrite Some_valid in Hvalid.
          rewrite <- (pair_op 1%Qp 1%Qp n recv_count) in Hvalid.
          rewrite pair_valid in Hvalid. destruct Hvalid as [Hqvalid _].
          rewrite frac_op in Hqvalid.
          assert (((1 + q)%Qp ≤ 1)%Qp) by done.
          apply Qp.not_add_le_l in H0.
          contradiction.
        }
        {
          iNamed "Hres". 
          iDestruct "Hres" as "(_ & %Hcontra & _ )". replace (W64 count) with (W64 0) in Hb by word.
          word.
        }
        {
          iNamed "Hres". iNamed "Hres". done.
        }
    }
    {
    + (* Case: Buffered channel (size = 0) with no data available *)
      destruct (vs =?= Valid_closed) eqn: Hc.
      {
        assert (vs = Valid_closed). {
          destruct vs. all: try done. 
        }
        subst vs.
        unfold recv_ctr_frozen. simpl. 
        (* TODO: use buffered lemma thing *)
        assert ((send_count =? recv_count) = true) by admit.
        rewrite H0. iDestruct "HSndCtrAuth" as "#HSndCtrAuth". 
        iDestruct "HRcvCtrAuth" as "#HRcvCtrAuth".

      wp_apply (wp_Channel__BufferedTryReceiveLocked ch γ chan_type size mu_l is_single_party Valid_closed
               count send_count recv_count first buff
               Psingle Pmulti Qsingle Qmulti R Ri i q
               with "[buff count chan_state HChanState first HRecvPerm HCloseTokPostClose]").
      *  done.
      * done.
      * rewrite Hb. unfold own_recv_perm. iFrame. iFrame "#". iNamed "HCloseTokPostClose". iFrame.
      simpl. rewrite H0. iFrame "#".
      iDestruct "HCloseTokPostClose" as "[Hctc HSen]".
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSen]") as "%Hag2". subst n.
        iFrame. iPureIntro. assert((W64 count) = (W64 0)) by word. 
        Search "unsigned_inj".
          assert (count + 1 < 2 ^ 63) by admit.
          word.
      * 
        
      iFrame.
       iIntros (success). iIntros (v0). iIntros (has_value). iIntros "Hres".
        wp_loadField. 
        wp_pures.
        destruct success eqn: Hqs, has_value eqn: Hqb.
        {
          iNamed "Hres". iNamed "Hres". unfold isBufferedChan. unfold isBufferedChanLogical.
          iNamed "HCh". unfold buff_size_inv.
          assert((W64 count) = (W64 0)) by word.
          assert (count + 1 < 2 ^ 63) by admit.
          assert (count = 0%nat) by word. 
          subst count. iDestruct "HCh" as "[Hoss HRest]".
       replace (0%nat - 1)%nat with (0%nat) by admit.
          iDestruct "HRest" as "(%H3 & %H4 & H5)". word.
          "[(Hoss & %Hsc & %Hsz & %Hl & %Hnf & %Hlx & %Hlxl & _)Hb]".
          word.
        wp_apply (wp_Mutex__Unlock with "[$Hlock HCh chan_state count value first HRecvCtrAuth HQ  $Hlocked]").
        {
            iModIntro.
            unfold isChanInner. 
            iExists vs, (count - 1)%nat, new_first, v, send_count, (S recv_count).
            iFrame. replace (W64 (count - 1)%nat) with (W64 (count-1)) by word.
            iFrame.    replace (Z.of_nat count - 1) with (Z.of_nat (count-1)) by word. iFrame.
        }
  
      (* Call BufferedTryReceive *)
        wp_loadField.
        wp_apply (wp_Mutex__Lock with "Hlock").
        iIntros "[Hlocked HisChanInner]". wp_pures.
        unfold isChanInner. iNamed "HisChanInner".
       (* destruct (vs =?= Valid_closed) eqn: Hc.
        {
          assert (vs = Valid_closed).
          { destruct vs. all: done. }
          replace vs with Valid_closed.
          subst vs. rewrite H. iNamed "HisChanInner".
        } *)
        
        (* Extract inner channel details *)
        iNamed "HisChanInner".

    }
   
        
            
          - (* Channel closed but tried to receive *)
            iNamed "Hres".
            iModIntro.
            iExists vs, 0%nat, first, v, send_count, recv_count.
            iFrame. rewrite H. iFrame. unfold recv_ctr_frozen. iFrame "#".
            iExists recv_count, (close_tok_names ∖ {[γr]}).
            iFrame "HScfroz HRcfroz HSc HCloseTokPostClose".
            rewrite Hsize_zero. iFrame.
            
          - (* No data available but channel not closed *)
            iDestruct "Hres" as "(Hchan_state & Hcount & Hfirst & HRcvPerm & HCh & %Hzero)".
            iModIntro.
            iExists vs, 0%nat, first, (zero_val chan_type), send_count, recv_count.
            iFrame "Hchan_state Hcount Hfirst HCh HRcvCtrAuth HSndCtrAuth HCloseTokPostClose".
            rewrite Hsize_zero. iFrame.
            
          - (* Impossible case *)
            by iDestruct "Hres" as "%contra".
        }
        
        wp_pures.
        
        (* Return appropriate results based on what happened *)
        destruct success, has_value.
        
        -- (* Successful receive with value *)
           iModIntro.
           iApply ("HΦ" $! v true true).
           iDestruct "Hres" as "(Hchan_state & %new_first & Hcount & Hfirst & HP & HRecvPerm & %HVt &
                                HCh & HRecvCtrAuth)".
           iFrame "HP HRecvPerm".
           iPureIntro. split; done.
        
        -- (* Channel closed but tried to receive *)
           iModIntro.
           iApply ("HΦ" $! (zero_val chan_type) false true).
           iDestruct "Hres" as "(Hchan_state & Hcount & Hfirst & HRi & #HScfroz & #HRcfroz & HSc & 
                                %close_tok_names & %γr & HCloseTokPostClose & %Hzero)".
           
           (* Extract the recv_counter_frag from HRcvPerm *)
           iNamed "HRcvPerm".
           iDestruct "HRcvPerm" as "[HRecvFrag HTok]".
           iFrame "HRecvFrag".
           iSplitR; first done.
           iSplitR; first done.
           iExists recv_count.
           iFrame "HRi HScfroz HRcfroz".
        
        -- (* No data available but channel not closed *)
           iModIntro.
           iApply ("HΦ" $! (zero_val chan_type) true false).
           iDestruct "Hres" as "(Hchan_state & Hcount & Hfirst & HRcvPerm & HCh & %Hzero)".
           iFrame "HQ HRcvPerm".
        
        -- (* Impossible case *)
           iDestruct "Hres" as "%contra".
           contradiction.

Lemma wp_Channel__TryReceive (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) 
  (size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) 
  (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri: nat -> iProp Σ) :
  (if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
  {{{ 
    "HCh" ∷ isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
    "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
    "HRecvPerm" ∷ own_recv_perm γ q i Ri 
  }}}
  Channel__TryReceive chan_type #ch
  {{{ (v: val) (ok: bool) (selected: bool), RET (#selected, v, #ok); 
    if selected then 
      (if ok then 
        ((P is_single_party i v Psingle Pmulti ∗ own_recv_perm γ q (i + 1) Ri ∗ ⌜ok⌝ ∗ ⌜val_ty v chan_type⌝))
      else
        (own_recv_counter_frag γ i q ∗ ⌜v = (zero_val chan_type)⌝ ∗ ⌜ok = false⌝
         ∗ ∃ n, (Ri n) ∗ own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true))
    else 
      (Q is_single_party i Qsingle Qmulti ∗ own_recv_perm γ q i Ri)
  }}}.
Proof.
  intros Hsp.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  
  wp_rec. wp_pures.
  iNamed "HCh".
  wp_loadField.
  
  (* Decide if channel is buffered or unbuffered *)
  wp_apply wp_slice_len.
  wp_if_destruct.
  
  (* Case: Buffered channel *)
  - wp_rec. 
    wp_pures.
    
    (* Lock channel *)
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked HisChanInner]".
    
    (* Extract inner channel details *)
    iNamed "HisChanInner".
    
    (* Check if channel has data (count > 0) *)
    wp_loadField.
    wp_pures.
    
    destruct (decide (word.unsigned count > 0)).
    + (* Case: Data available - successful receive *)
      wp_if_destruct; first last; [contradiction|].
      
      (* Extract value and update channel state *)
      wp_loadField.
      wp_loadField.
      wp_apply (wp_SliceGet with "[$HBuffUnbuff]"); first val_ty.
      { destruct size; [done|]. iNamed "HBuffUnbuff". done. }
      iIntros "HBuffUnbuff".
      
      wp_store.
      wp_loadField.
      wp_loadField.
      wp_loadField.
      wp_op.
      wp_loadField.
      wp_apply wp_slice_len.
      wp_op.
      wp_storeField.
      
      wp_loadField.
      wp_op.
      wp_storeField.
      
      (* Load value and return *)
      wp_load.
      wp_pures.
      
      (* Update state and release lock *)
      iAssert (∃ v0, P is_single_party i v0 Psingle Pmulti ∗ ⌜val_ty v0 chan_type⌝)%I
        with "[HBuffUnbuff]" as (v0) "[HP #Hvty]".
      { destruct size; [done|].
        iNamed "HBuffUnbuff".
        unfold isBufferedChan.
        iDestruct "HBuffUnbuff" as "[Hbuff HLogical]".
        iDestruct "HLogical" as "(%Hcount & %Hsize & %Hfirst & HPs & HQs)".
        iDestruct (array_cons with "HPs") as "[HP HPs']".
        iExists _. iFrame. iPureIntro. done. }
      
      (* Unlock mutex *)
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked value chan_state count first HSndCtrAuth HRcvCtrAuth HCloseTokPostClose HBuffUnbuff]").
      { iModIntro. iExists vs, (word.sub count (W64 1)), first, v0, send_count, (recv_count + 1).
        iFrame. destruct vs; try iFrame "#"; done. }
      
      wp_pures.
      iModIntro.
      iApply ("HΦ" $! v0 true true).
      iSplitL "HP".
      * iFrame "HP". iSplitL "HRecvPerm".
        -- replace (i + 1)%nat with (S i) by lia. iFrame.
        -- iPureIntro. split; done.
      * iFrame.
      
    + (* Case: No data available *)
      wp_if_destruct; first [|contradiction].
      
      (* Check if channel is closed *)
      wp_loadField.
      wp_pures.
      
      destruct (decide (vs = Valid_closed)).
      * (* Channel is closed *)
        wp_if_destruct; first [|subst vs; contradiction].
        wp_load.
        wp_pures.
        
        (* Extract closed channel resources *)
        iAssert (∃ n close_tok_names,
          own_closed_tok_post_close γ n close_tok_names ∗
          own_send_counter_frag γ n 1 ∗
          own_send_counter_auth γ n true)%I
          with "[HCloseTokPostClose]" as (n close_tok_names) "(Htok & Hsnd & #Hauth)".
        { subst vs. iNamed "HCloseTokPostClose". iExists n, close_tok_names. iFrame. iFrame "#". }
        
        (* Release lock *)
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked value chan_state count first HSndCtrAuth HRcvCtrAuth HBuffUnbuff]").
        { iModIntro. iExists Valid_closed, count, first, v, send_count, recv_count.
          iFrame. iExists n, close_tok_names. iFrame. iFrame "#". }
        
        wp_pures.
        iModIntro.
        iApply ("HΦ" $! (zero_val chan_type) false true).
        
        (* Return resources for closed channel *)
        iNamed "HRecvPerm".
        iDestruct "HRecvPerm" as "[Hfrag Htok']".
        iFrame "Hfrag".
        iSplitL ""; first done.
        iSplitL ""; first done.
        iExists n. iFrame "Htok' Hauth".
        
        (* Need to derive recv_counter_auth for n *)
        iAssert (own_recv_counter_auth γ n true)%I as "#Hrecv_auth".
        { (* This would come from channel invariant when n = recv_count *) admit. }
        
        iFrame "Hrecv_auth".
      
      * (* Channel not closed but empty *)
        wp_if_destruct; first [contradiction|].
        wp_load.
        wp_pures.
        
        (* Release lock *)
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked value chan_state count first HSndCtrAuth HRcvCtrAuth HCloseTokPostClose HBuffUnbuff]").
        { iModIntro. iExists vs, count, first, v, send_count, recv_count.
          iFrame. destruct vs; try iFrame "#"; done. }
        
        wp_pures.
        iModIntro.
        iApply ("HΦ" $! (zero_val chan_type) true false).
        iFrame.
  
  (* Case: Unbuffered channel *)
  - wp_apply wp_ref_of_zero; first done.
    iIntros (local_val) "Hval".
    wp_pures.
    
    (* Extract channel components *)
    iNamed "HCh".
    
    (* Lock channel *)
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked HisChanInner]".
    
    (* Extract inner channel details *)
    iNamed "HisChanInner".
    
    (* Assert size = 0 for unbuffered channel *)
    assert (size = 0)%nat as Hsize0.
    { destruct size; [done|]. simpl in Heqb. discriminate. }
    rewrite Hsize0 in *.
    
    (* Apply ReceiverCompleteOrOffer *)
    wp_pures.
    wp_apply (wp_Channel__ReceiverCompleteOrOffer ch i q γ chan_type buff v send_count recv_count vs 0%nat is_single_party Psingle Pmulti Qsingle Qmulti R Ri
              with "[chan_state value HQ HRecvPerm HRcvCtrAuth HBuffUnbuff]").
    { exact Hsp. }
    { rewrite Hsize0. simpl. done. }
    { iFrame. rewrite Hsize0 in HBuffUnbuff. iFrame. }
    
    iIntros (res) "Hres".
    wp_pures.
    
    (* Handle result from ReceiverCompleteOrOffer *)
    wp_apply wp_ref_to; first val_ty.
    iIntros (ok_ptr) "Hok".
    
    wp_pures.
    wp_op.
    
    destruct res.
    
    + (* ReceiverCompletedWithSender *)
      wp_if_destruct; first [|contradiction].
      wp_apply wp_ref_to; first val_ty.
      iIntros (selected_ptr) "Hselected".
      wp_pures.
      wp_op.
      wp_op.
      wp_if_destruct; first [|contradiction].
      
      (* Load value from channel *)
      wp_loadField.
      wp_store.
      wp_pures.
      
      (* Unlock mutex *)
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hres]").
      { iNamed "Hres". iModIntro. iExists Valid_receiver_done, count, first, v, send_count, (recv_count + 1).
        iFrame. rewrite Hsize0. iFrame. }
      
      wp_pures.
      wp_load.
      wp_pures.
      wp_load.
      wp_load.
      wp_pures.
      
      iModIntro.
      iApply ("HΦ" $! v true true).
      iNamed "Hres".
      
      iAssert (P is_single_party i v Psingle Pmulti)%I with "[HCh]" as "HP".
      { unfold isUnbufferedChan in HCh.
        iDestruct "HCh" as "[%HFacts HRes]".
        destruct HFacts.
        unfold chan_state_resources in HRes.
        destruct is_single_party; simpl in *; iFrame. }
      
      iFrame "HP HRecvPerm".
      iPureIntro. split; [done|].
      destruct vs; try done.
    
    + (* ReceiverMadeOffer *)
      wp_if_destruct; first [contradiction|].
      wp_apply wp_ref_to; first val_ty.
      iIntros (selected_ptr) "Hselected".
      wp_pures.
      wp_op.
      wp_op.
      wp_if_destruct; first [contradiction|].
      
      (* Unlock mutex *)
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hres]").
      { iNamed "Hres". iModIntro. iExists Valid_receiver_ready, count, first, v, send_count, recv_count.
        iFrame. rewrite Hsize0. iFrame. }
      
      wp_pures.
      wp_if_destruct; first [|contradiction].
      
      (* Lock channel to check offer result *)
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked HisChanInner]".
      
      (* Apply ReceiverCompleteOrRescindOffer *)
      wp_pures.
      wp_apply (wp_Channel__ReceiverCompleteOrRescindOffer ch i q γ chan_type buff v send_count recv_count Valid_receiver_ready 0%nat is_single_party Psingle Pmulti Qsingle Qmulti R Ri
                with "[chan_state value HisChanInner Hsttok]").
      { exact Hsp. }
      { rewrite Hsize0. simpl. done. }
      { left. done. }
      { iNamed "Hres".
        iNamed "HisChanInner".
        iFrame "chan_state value".
        iAssert (isUnbufferedChan ch γ chan_type v Valid_receiver_ready is_single_party send_count recv_count
                Psingle Pmulti Qsingle Qmulti R)%I with "[HCh]" as "HCh".
        { iFrame. }
        iFrame "HCh HRecvCtrAuth Hsttok HRecvPerm".
        iSplitL ""; first done. }
      
      iIntros (offer_res) "Hoffer".
      wp_pures.
      
      destruct offer_res.
      
      * (* OfferRescinded *)
        wp_if_destruct; first [contradiction|].
        
        (* Unlock mutex *)
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hoffer]").
        { iNamed "Hoffer". iModIntro. iExists Valid_start, count, first, v, send_count, recv_count.
          iFrame. rewrite Hsize0. iFrame. }
        
        wp_pures.
        wp_load.
        wp_load.
        wp_load.
        wp_pures.
        
        iModIntro.
        iApply ("HΦ" $! (zero_val chan_type) true false).
        iNamed "Hoffer".
        iFrame "HQ HRecvPerm".
      
      * (* CompletedExchange *)
        wp_if_destruct; first [|contradiction].
        
        (* Load value from channel *)
        wp_loadField.
        wp_store.
        wp_pures.
        wp_store.
        
        (* Unlock mutex *)
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hoffer]").
        { iNamed "Hoffer". iModIntro. iExists Valid_start, count, first, v, send_count, (recv_count + 1).
          iFrame. rewrite Hsize0. iFrame. }
        
        wp_pures.
        wp_load.
        wp_load.
        wp_load.
        wp_pures.
        
        iModIntro.
        iApply ("HΦ" $! v true true).
        iNamed "Hoffer".
        iFrame "HP HRecvPerm".
        iPureIntro. split; done.
      
      * (* CloseInterruptedOffer - impossible case *)
        iNamed "Hoffer".
        done.
    
    + (* ReceiverObservedClosed *)
      wp_if_destruct; first [contradiction|].
      wp_apply wp_ref_to; first val_ty.
      iIntros (selected_ptr) "Hselected".
      wp_pures.
      wp_op.
      wp_op.
      wp_if_destruct; first [|contradiction].
      
      (* Load zero value *)
      wp_loadField.
      wp_store.
      wp_pures.
      
      (* Extract closed channel resources *)
      iAssert (∃ n close_tok_names,
        own_closed_tok_post_close γ n close_tok_names ∗
        own_send_counter_frag γ n 1 ∗
        own_send_counter_auth γ n true)%I
        with "[HCloseTokPostClose]" as (n close_tok_names) "(Htok & Hsnd & #Hauth)".
      { iNamed "HCloseTokPostClose". iExists n, close_tok_names. iFrame. iFrame "#". }
      
      (* Unlock mutex *)
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked chan_state]").
      { iModIntro. iExists Valid_closed, count, first, v, send_count, recv_count.
        iFrame "chan_state". iExists n, close_tok_names. iFrame "Htok Hsnd". iFrame "#". }
      
      wp_pures.
      wp_if_destruct; first [contradiction|].
      wp_load.
      wp_load.
      wp_load.
      wp_pures.
      
      iModIntro.
      iApply ("HΦ" $! (zero_val chan_type) false true).
      
      (* Return resources for closed channel *)
      iNamed "HRecvPerm".
      iDestruct "HRecvPerm" as "[Hfrag Htok']".
      iFrame "Hfrag".
      iSplitL ""; first done.
      iSplitL ""; first done.
      iExists n. iFrame "Htok' Hauth".
      
      (* Need to derive recv_counter_auth for n *)
      iAssert (own_recv_counter_auth γ n true)%I as "#Hrecv_auth".
      { (* This would come from channel invariant when n = recv_count *) admit. }
      
      iFrame "Hrecv_auth".
    
    + (* ReceiverCannotProceed *)
      wp_if_destruct; first [contradiction|].
      wp_apply wp_ref_to; first val_ty.
      iIntros (selected_ptr) "Hselected".
      wp_pures.
      wp_op.
      wp_op.
      wp_if_destruct; first [contradiction|].
      
      (* Unlock mutex *)
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hres]").
      { iNamed "Hres". iModIntro. iExists vs, count, first, v, send_count, recv_count.
        iFrame. rewrite Hsize0. iFrame. }
      
      wp_pures.
      wp_if_destruct; first [contradiction|].
      wp_load.
      wp_load.
      wp_load.
      wp_pures.
      
      iModIntro.
      iApply ("HΦ" $! (zero_val chan_type) true false).
      iNamed "Hres".
      iFrame.
Admitted.

Lemma wp_Channel__TrySend (ch: loc) (i: nat) (v: val) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) 
(Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :

val_ty v chan_type -> 
#ch ≠ #null ->
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
size + 1 < 2 ^ 63 ->

{{{ 
  "HCh" ∷ isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  "HP" ∷ P is_single_party i v Psingle Pmulti ∗ 
  "HSc" ∷ own_send_counter_frag γ i q
}}}
Channel__TrySend chan_type #ch v
{{{ (selected: bool), RET #selected; 
  if selected then 
    (Q is_single_party (i - size) Qsingle Qmulti ∗ own_send_counter_frag γ (i + 1)%nat q)
  else 
    (P is_single_party i v Psingle Pmulti ∗ own_send_counter_frag γ i q)
}}}.
Proof.
  intros Hvt Hnn Hsp Hsgt64.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  iNamed "HCh".
  
  wp_rec. wp_pures.
  wp_loadField. wp_pures.
  wp_apply wp_slice_len.
  wp_apply wp_ref_to; first val_ty.
  iIntros (buffer_size_ptr) "Hbuffer_size".
  wp_pures. wp_load.
  
  wp_if_destruct.
  
  - (* Case: Buffered channel (size > 0) *)
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked HisChanInner]". wp_pures.
    
    (* Extract the inner channel details *)
    iDestruct "HisChanInner" as (vs count' first' v' send_count' recv_count') 
      "(Hvalue & Hchan_state & Hcount & Hfirst & HSndCtrAuth' & HRecvCtrAuth & HCloseTokPostClose & HChanState)".
    
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
               apply Qp.not_add_le_l in H.
               contradiction.
    }
    
    (* Identify channel state as buffered *)
    assert (size > 0)%nat as Hsize_pos by word.
    assert ((size =? 0) = false) by lia.
    rewrite H. iNamed "HChanState". unfold isBufferedChan.
    iNamed "HChanState". iDestruct "HChanState" as "(Hoss & Hfax)".
    unfold isBufferedChanLogical.
    iDestruct "Hfax" as "(%Hct & %Hsz & %Hbs & HPs & HQs )".

    wp_apply (wp_Channel__BufferedTrySend ch v  γ chan_type buff is_single_party q first' size count'
                  vs send_count' recv_count' Psingle Pmulti Qsingle Qmulti R i with 
                  "[HP HSc HSndCtrAuth' Hchan_state Hcount HPs HQs Hoss  Hfirst]").
                  all: try done.
        { inversion Hbuffsize. done. }
        { word. }
        { word.  }
        { iFrame. iFrame "#".  unfold send_ctr_frozen. 
        destruct vs. all: try (iFrame;iPureIntro;word).
        exfalso. apply Hnot_closed. done.
        }
        iIntros (success) "IH". 
        destruct success.
        {
          
         iNamed "IH". wp_pures. wp_loadField.
         wp_apply (wp_Mutex__Unlock with
          "[$Hlock chan_state count first Hvalue HRecvCtrAuth HSndCtrAuth HCh $Hlocked]").
        { iModIntro. unfold isChanInner. iExists vs, (S count'), first', v', (S send_count'), recv_count'. unfold send_ctr_frozen. rewrite H. iFrame. unfold recv_ctr_frozen.
        destruct (vs =?= Valid_closed) eqn: H0.
        {
         assert (vs = Valid_closed).
         { destruct vs. all: try done. }
         subst vs. contradiction. 
        }
        destruct vs. all: try iFrame;done.
        }
        wp_pures.
        iApply "HΦ". iModIntro.
        replace (i + 1)%nat with (S i) by lia.
        iFrame.
        }
        {
          iNamed "IH".

        iAssert (own_send_counter_auth γ send_count' false ∗ 
                own_send_counter_frag γ i q ∗ 
                ⌜if is_single_party then send_count' = i else i <= send_count'⌝%I)%I
          with "[HSndCtrAuth HSen]" as "(HSndCtrAuth & HSen & %Hispz)".
        {
          destruct is_single_party.
          - subst q.
            iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSen]") as "%Hag2".
            iFrame. iPureIntro. done.
          - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSen]") as "%Hag2".
            iFrame. iPureIntro. lia.
        }
           
          wp_pures. wp_loadField.
         wp_apply (wp_Mutex__Unlock with
          "[$Hlock chan_state count first Hvalue HRecvCtrAuth HSndCtrAuth HCh $Hlocked]").
          { 
            iModIntro. unfold isChanInner. iExists vs, (count'), first', v', (send_count'), recv_count'. unfold send_ctr_frozen. rewrite H. iFrame. unfold recv_ctr_frozen.
        destruct (vs =?= Valid_closed) eqn: H0.
        {
        assert (vs = Valid_closed).
        { destruct vs. all: try done. }
        subst vs. contradiction. 
       }
       destruct vs. all: try iFrame;done.
       }
       wp_pures.
       iApply "HΦ". iModIntro.
       replace (i + 1)%nat with (S i) by lia.
       iFrame.

        }


  - (* Case: Unbuffered channel (size = 0) *)
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked HisChanInner]". wp_pures.
    
    (* Extract the inner channel details *)
    iDestruct "HisChanInner" as (vs count' first' v' send_count' recv_count') 
      "(Hvalue & Hchan_state & Hcount & Hfirst & HSndCtrAuth' & HRecvCtrAuth & HCloseTokPostClose & HChanState)".
    
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
               apply Qp.not_add_le_l in H.
               contradiction.
    }
    
    (* Identify channel is unbuffered *)
    assert ((size =? 0) = true).
    {
      word.
    }
    assert (size = 0)%nat as Hsize_zero.
    {
      word.
    }
    destruct (decide (size = 0%nat)); last by (exfalso; lia).
    
    (* Apply SenderCompleteOrOffer *)
    iDestruct "HChanState" as "HUnbuffCh".
    
    wp_pures.
    iDestruct (struct_field_pointsto_ty with "[$Hvalue]") as "%Hvty".
    {
     simpl. done. 
    }
    wp_apply (wp_Channel__SenderCompleteOrOffer ch v v' γ chan_type buff vs
              send_count' recv_count' 0%nat is_single_party Psingle Pmulti
              Qsingle Qmulti R _ i q with "[Hvalue HUnbuffCh Hchan_state HP HSndCtrAuth' HSc]").
              all: (try done;try word; try lia; try iFrame).
    { replace ((W64 0)) with ((W64 0%nat)) by word.  inversion Hbuffsize.
    subst size. inversion H1. done.
    }
    { rewrite H.  (* Frame resources *) iFrame. }
    
    iIntros (res) "Hres".
    
    
    (* Release mutex *)
    wp_loadField.
    
    (* Branch based on sender result *)
    destruct res, vs.
    
    + (* SenderCompletedWithReceiver, Valid_start - impossible combination *)
      done.
    
    + (* SenderCompletedWithReceiver, Valid_receiver_ready *)
      iNamed "Hres".
      
      (* Release mutex *)
      wp_apply (wp_Mutex__Unlock with "[$Hlock value chan_state Hcount HSndCtrAuth HRecvCtrAuth 
       HCloseTokPostClose HCh $Hlocked]").
      {
        iModIntro. unfold isChanInner. 
        iExists Valid_sender_done, count', first', v, (S send_count'), recv_count'.
        iFrame. rewrite H. iFrame. replace (send_count' + 1)%nat with (S send_count') by lia.
        iFrame.
      }
      
      (* Return success *)
      wp_pures. iModIntro. 
      
      iApply "HΦ". simpl. iFrame. subst size. replace (i - 0%nat) with (Z.of_nat i) by lia.
      iFrame.

    (* More cases - will be admitted for brevity *)
    + done.
    + done.
    + done.
    + done.
    
    (* SenderMadeOffer, Valid_start - check offer result *)
    + iDestruct "Hres" as "(Hvalue & HCh & Hchan_state & HSndCtrAuth' & HSen & Hsttok)".
      
      (* Release mutex *)
      wp_apply (wp_Mutex__Unlock with "[$Hlock Hvalue Hcount Hchan_state HSndCtrAuth' HRecvCtrAuth 
       HCloseTokPostClose HCh $Hlocked]").
      {
        iModIntro.
        iExists Valid_sender_ready, count', first', v, send_count', recv_count'.
        iFrame. rewrite H. iFrame.
      }
      
      (* Check offer result *)
      wp_pures. wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock"). 
      iIntros "[locked inv]". wp_pures.

      unfold isChanInner.
      iNamed "inv". rewrite H. iDestruct "inv" as "[Hemp inv]". iNamed "inv".
      destruct (decide (vs =?= Valid_closed)) as [Heq|Hneq].
{
  replace vs with Valid_closed.
  {
   iNamed "HCloseTokPostClose". iDestruct "HCloseTokPostClose" as "[Hct1 Hct2]".
   iDestruct (own_valid_2 with "[$Hct2] [$HSen]") as "%Hvalid". 
   apply auth_frag_op_valid_1 in Hvalid.
  rewrite <- (Some_op (1%Qp, n) (q, i)) in Hvalid.
  rewrite Some_valid in Hvalid.
  rewrite <- (pair_op 1%Qp q n i) in Hvalid.
  rewrite pair_valid in Hvalid. destruct Hvalid as [Hqvalid _].
  rewrite frac_op in Hqvalid.
  assert (((1 + q)%Qp ≤ 1)%Qp) by done.
  apply Qp.not_add_le_l in H0.
  contradiction.
  }
  {
    destruct vs. all: done.
  }
}
      
      iDestruct (( sender_token_state_agree γ ch v vs send_count recv_count v0 chan_type
      is_single_party Psingle Pmulti Qsingle Qmulti R ) with " [Hsttok] [HChanState]") as "%Hct".
      {
         destruct vs. all: done.
      }
      {
       iFrame. 
      }
      {
       iFrame. 
      }
      destruct Hct as [Hvsr Hvv0].
      
      
      unfold isUnbufferedChan. unfold chan_state_resources.
        iAssert (own_send_counter_auth γ send_count (send_ctr_frozen vs) ∗ 
                own_send_counter_frag γ i q ∗ 
                ⌜if is_single_party then send_count = i else i <= send_count⌝%I)%I
          with "[HSndCtrAuth HSen]" as "(HSndCtrAuth & HSen & %Hispz)".
        {
          destruct is_single_party.
          - subst q.
            iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSen]") as "%Hag2".
            iFrame. iPureIntro. lia.  
          - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSen]") as "%Hag2".
            iFrame. iPureIntro. lia. 
        }
      
      wp_apply (wp_Channel__SenderCheckOfferResult ch v  γ chan_type buff 
              send_count recv_count vs 0%nat is_single_party Psingle Pmulti
              Qsingle Qmulti R _ i q with "[ HCloseTokPostClose HSndCtrAuth HChanState chan_state value Hsttok HSen]").
              all: (try done;try word; try lia; try iFrame).
    { replace ((W64 0)) with ((W64 0%nat)) by word.  inversion Hbuffsize.
    subst size. inversion H1. done.
    }
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
    {
    replace v0 with v by done. iFrame. 
      
    }
    iIntros (res) "Hvs". destruct res.
    {
     simpl. wp_loadField.  
     destruct vs. all: try done. iNamed "Hvs".
     wp_apply (wp_Mutex__Unlock with "[$Hlock HRcvCtrAuth count  HSndCtrAuth value chan_state 
        HCh $locked]").
      {
        iModIntro. iExists Valid_start. iFrame. iExists (W64 0). done.
      }
      wp_pures. iModIntro. iApply "HΦ". iFrame.
      unfold P. destruct is_single_party.
      {
        subst send_count.
       iFrame. 
      }
      unfold P. done.
     
    }
    {
      simpl. wp_loadField.  
      destruct vs. all: try done. iNamed "Hvs".
      wp_apply (wp_Mutex__Unlock with "[$Hlock HRcvCtrAuth count  HSndCtrAuth value chan_state 
         HCh $locked]").
       {
         iModIntro. iExists Valid_start. iFrame. iExists (W64 0). done.
       }
       wp_pures. iModIntro. iApply "HΦ". iFrame.
       unfold P. destruct is_single_party.
       {
         subst send_count.
        iFrame. subst size. replace (i - 0%nat) with (Z.of_nat i) by lia. done.
       }
        iFrame. subst size. replace (i - 0%nat) with (Z.of_nat i) by lia. done.

    }
    {
     wp_pures.  
     simpl. wp_loadField.  
      destruct vs. all: try done. 
    }
    + done.
    + done.
    + done.
    + done.
    + done.
    (* what are these last 2 cases *)
    + iNamed "Hres".
    
    wp_apply (wp_Mutex__Unlock with "[$Hlock HRecvCtrAuth Hcount Hfirst  HSndCtrAuth value chan_state 
    HCh $Hlocked]").
  {
    iModIntro. iFrame. rewrite H. iFrame. done.  
  }
  {
   wp_pures. iModIntro. iApply "HΦ". iFrame. 
  }
    + iNamed "Hres".
    
    wp_apply (wp_Mutex__Unlock with "[$Hlock HRecvCtrAuth Hcount Hfirst  HSndCtrAuth value chan_state 
    HCh $Hlocked]").
  {
    iModIntro. iFrame. rewrite H. iFrame. done.  
  }
  {
   wp_pures. iModIntro. iApply "HΦ". iFrame. 
  }
  + iNamed "Hres".
    
  wp_apply (wp_Mutex__Unlock with "[$Hlock HRecvCtrAuth Hcount Hfirst  HSndCtrAuth value chan_state 
  HCh $Hlocked]").
{
  iModIntro. iFrame. rewrite H. iFrame. done.  
}
{
 wp_pures. iModIntro. iApply "HΦ". iFrame. 
}
  + iNamed "Hres".
  
  wp_apply (wp_Mutex__Unlock with "[$Hlock HRecvCtrAuth Hcount Hfirst  HSndCtrAuth value chan_state 
  HCh $Hlocked]").
{
  iModIntro. iFrame. rewrite H. iFrame. done.  
}
{
 wp_pures. iModIntro. iApply "HΦ". iFrame. 
}
+ iNamed "Hres".
    
wp_apply (wp_Mutex__Unlock with "[$Hlock HRecvCtrAuth Hcount Hfirst  HSndCtrAuth value chan_state 
HCh $Hlocked]").
{
iModIntro. iFrame. rewrite H. iFrame. done.  
}
{
wp_pures. iModIntro. iApply "HΦ". iFrame. 
}
+ iNamed "Hres".

wp_apply (wp_Mutex__Unlock with "[$Hlock HRecvCtrAuth Hcount Hfirst  HSndCtrAuth value chan_state 
HCh $Hlocked]").
{
iModIntro. iFrame. rewrite H. iFrame. done.  
}
{
wp_pures. iModIntro. iApply "HΦ". iFrame. 
}
Unshelve.
{ done. } { done. } 
Qed.

End proof.