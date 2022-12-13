From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import eesm.
From Perennial.program_proof Require Import marshal_stateless_proof.
From iris.base_logic Require Import ghost_map.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.simplepb Require Import pb_definitions.
From Perennial.program_proof.simplepb Require Import pb_apply_proof clerk_proof.
From Perennial.program_proof.grove_shared Require Import erpc_lib.
From Perennial.program_proof Require Import map_marshal_proof.
From iris.algebra Require Import dfrac_agree mono_list.

Section global_proof.

Context `{low_record:PBRecord}.

Notation low_OpType := (pb_OpType low_record).
Notation low_has_op_encoding := (pb_has_op_encoding low_record).
Notation low_has_snap_encoding := (pb_has_snap_encoding low_record).
Notation low_compute_reply := (pb_compute_reply low_record).
Instance low_op_eqdec : EqDecision low_OpType.
Proof. apply (pb_OpType_EqDecision low_record). Qed.

Inductive eeOp :=
  | getcid : eeOp
  | ee : u64 → u64 -> low_OpType → eeOp
.

Inductive eeState :=
  | ees : u64 → gmap u64 u64 → gmap u64 (list u8) → list low_OpType → eeState
.

Definition apply_op_and_get_reply (state:eeState) (op:eeOp) : eeState * list u8 :=
  match state with
  | ees nextCID lastSeq lastReply ops =>
      match op with
      | getcid => (ees (word.add nextCID 1) lastSeq lastReply ops, u64_le nextCID)
      | ee cid seq op =>
          if decide (int.nat seq <= int.nat (default (U64 0) (lastSeq !! cid))) then
            (state, default [] (lastReply !! cid))
          else
            let rep:=(low_compute_reply ops op) in
            (ees nextCID (<[cid:=seq]>lastSeq)
                 (<[cid:=rep]>lastReply) (ops ++ [op]), rep)
      end
  end
.

Definition apply_op state op :=
  (apply_op_and_get_reply state op).1
.

Definition init_state := ees 0 ∅ ∅ [].

Definition compute_state ops : eeState :=
  foldl apply_op init_state ops.

Definition compute_reply ops op : (list u8) :=
  (apply_op_and_get_reply (compute_state ops) op).2
.

Definition ee_has_encoding op_bytes op :=
  match op with
  | getcid => op_bytes = [U8 1]
  | ee cid seq lowop =>
      ∃ lowop_enc,
  low_has_op_encoding lowop_enc lowop ∧
  op_bytes = [U8 0] ++ u64_le cid ++ u64_le seq ++ (lowop_enc)
  end
.

Definition ee_has_snap_encoding snap_bytes ops :=
  let st := (compute_state ops) in
  match st with
  | ees nextCID lastSeq lastReply lowops =>
      ∃ low_snap_bytes enc_lastSeq enc_lastReply,
      has_u64_map_encoding enc_lastSeq lastSeq ∧
      has_byte_map_encoding enc_lastReply lastReply ∧
      low_has_snap_encoding low_snap_bytes lowops ∧
      snap_bytes = (u64_le nextCID) ++ (enc_lastSeq) ++ enc_lastReply ++ low_snap_bytes
  end
.

Instance op_eqdec : EqDecision eeOp.
Proof. solve_decision. Qed.

Definition
  ee_record:=
  {|
    pb_OpType := eeOp ;
    pb_has_op_encoding := ee_has_encoding ;
    pb_has_snap_encoding := ee_has_snap_encoding ;
    pb_compute_reply :=  compute_reply ;
  |}.

Context `{!inG Σ (mono_listR (leibnizO low_OpType))}.
Context `{!pbG (pb_record:=ee_record) Σ}.

Definition own_oplog γ (lowops:list low_OpType) := own γ (●ML{#1/2} (lowops : list (leibnizO _))).

Context `{!gooseGlobalGS Σ, !urpcregG Σ, !erpcG Σ (list u8)}.
Definition own_eeState st γ γerpc : iProp Σ :=
  match st with
  | ees nextCID lastSeq lastReply lowops =>
      "Hlog" ∷ own_oplog γ lowops ∗
      "HerpcServer" ∷ eRPCServer_own_ghost γerpc lastSeq lastReply ∗
      "Hcids" ∷ ([∗ set] cid ∈ (fin_to_set u64), ⌜int.Z cid < int.Z nextCID⌝%Z ∨
                                                  (is_eRPCClient_ghost γerpc cid 1))
  end
.

Definition eeN := nroot .@ "ee".

Notation own_log := (own_log (pb_record:=ee_record)).

Definition is_ee_inv γpblog γ γerpc : iProp Σ :=
  inv eeN (∃ ops,
              own_log γpblog ops ∗
              own_eeState (compute_state ops) γ γerpc
      )
.

End global_proof.

Section local_proof.

Context `{low_record:PBRecord}.
Notation low_OpType := (pb_OpType low_record).
Notation low_has_op_encoding := (pb_has_op_encoding low_record).
Notation low_compute_reply := (pb_compute_reply low_record).
Instance low_op_dec2 : EqDecision low_OpType.
Proof. apply (pb_OpType_EqDecision low_record). Qed.

Context `{!heapGS Σ, !urpcregG Σ, !erpcG Σ (list u8)}.

Notation ee_record := (ee_record (low_record:=low_record)).
Notation compute_state := (compute_state (low_record:=low_record)).
Notation eeOp := (eeOp (low_record:=low_record)).
Notation ee_is_InMemoryStateMachine := (is_InMemoryStateMachine (sm_record:=ee_record)).
Notation low_is_InMemoryStateMachine := (is_InMemoryStateMachine (sm_record:=low_record)).
Notation own_pb_Clerk := (clerk_proof.own_Clerk (pb_record:=ee_record)).
Notation is_ee_inv := (is_ee_inv (low_record:=low_record)).

Context `{!config_proof.configG Σ}.
Context `{!inG Σ (mono_listR (leibnizO low_OpType))}.
Context `{!pbG (pb_record:=ee_record) Σ}.

Definition own_Clerk ck γoplog : iProp Σ :=
  ∃ (pb_ck:loc) γpblog γerpc (cid seqno:u64),
    "Hcid" ∷ ck ↦[eesm.Clerk :: "cid"] #cid ∗
    "Hseq" ∷ ck ↦[eesm.Clerk :: "seq"] #seqno ∗
    "Hown_ck" ∷ own_pb_Clerk pb_ck γpblog ∗
    "#Hpb_ck" ∷ readonly (ck ↦[eesm.Clerk :: "ck"] #pb_ck) ∗
    "#Hee_inv" ∷ is_ee_inv γpblog γoplog γerpc ∗
    "Herpc" ∷ is_eRPCClient_ghost γerpc cid seqno ∗
    "#Herpc_inv" ∷ is_eRPCServer γerpc ∗
    "%Hseqno_pos" ∷ ⌜ int.nat seqno > 0 ⌝
.

Lemma compute_state_snoc ops newop :
  compute_state (ops ++ [newop]) = apply_op (compute_state ops) newop.
Proof.
  unfold compute_state. by rewrite foldl_snoc.
Qed.


Lemma wp_Clerk__ApplyExactlyOnce ck γoplog lowop op_sl lowop_bytes Φ:
  low_has_op_encoding lowop_bytes lowop →
  own_Clerk ck γoplog -∗
  is_slice op_sl byteT 1 lowop_bytes -∗
  (|={⊤∖↑pbN∖↑eeN,∅}=> ∃ oldops, own_oplog γoplog oldops ∗
    (own_oplog γoplog (oldops ++ [lowop]) ={∅,⊤∖↑pbN∖↑eeN}=∗
    (∀ reply_sl, own_Clerk ck γoplog -∗ is_slice_small reply_sl byteT 1 (low_compute_reply oldops lowop)
     -∗ Φ (slice_val reply_sl )))) -∗
  WP Clerk__ApplyExactlyOnce #ck (slice_val op_sl) {{ Φ }}.
Proof.
  intros Henc.
  iIntros "Hclerk Hop Hupd".
  iNamed "Hclerk".

  wp_call.
  wp_apply (wp_NewSliceWithCap).
  { word. }
  iIntros (?) "Henc_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pure1_credit "Hlc".
  wp_pure1_credit "Hlc2".
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_store.

  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_store.

  wp_load.
  iDestruct (is_slice_to_small with "Hop") as "Hop".
  wp_apply (wp_WriteBytes with "[$Henc_sl $Hop]").
  iIntros (?) "[Henc_sl _]".
  wp_store.
  wp_loadField.
  wp_apply (std_proof.wp_SumAssumeNoOverflow).
  iIntros (Hseqno_overflow).
  wp_storeField.
  wp_load.

  wp_loadField.

  iMod (make_request ({| Req_CID:= _; Req_Seq:= _ |}) with "Herpc_inv Herpc [Hupd Hlc]") as "[Herpc Hreq]".
  { done. }
  { simpl. word. }
  {
    iNext.
    iNamedAccu.
  }
  instantiate(1:=
          (λ reply, ∀ reply_sl,
            own_Clerk ck γoplog -∗
            is_slice_small reply_sl byteT 1 reply -∗
            Φ (slice_val reply_sl))
        %I).
  (* assert that it equals low_compute_reply *)

  iDestruct "Hreq" as (?) "(#Hreq & Htok)".
  iApply wp_fupd.
  iApply (wp_frame_wand with "[Hcid Hseq Herpc Htok Hlc2]").
  { iNamedAccu. }
  simpl.
  iDestruct (is_slice_to_small with "Henc_sl") as "Henc_sl".
  wp_apply (wp_Clerk__Apply with "Hown_ck [$Henc_sl]").
  {
    simpl.
    rewrite -app_assoc.
    rewrite -app_assoc.
    instantiate (1:= ee cid seqno lowop).
    exists lowop_bytes.
    split; done.
  }
  {
    iModIntro.
    iInv "Hee_inv" as "Hi" "Hclose".
    iDestruct "Hi" as (?) "[>Hpblog Hee]".
    set (st:=compute_state ops).
    destruct st eqn:X.
    iDestruct "Hee" as ">Hee".
    iNamed "Hee".


    destruct (decide (int.Z (default (U64 0) (g !! cid)) < int.Z seqno)%Z).
    { (* case: first time running request *)
      iMod (server_takes_request with "Hreq HerpcServer") as "HH".
      {
        simpl.
        assert (↑rpcRequestInvN {| Req_CID := cid; Req_Seq := seqno |} ## (↑pbN:coPset)).
        {
          unfold rpcRequestInvN.
          unfold pbN.
          simpl.
          apply ndot_preserve_disjoint_l.
          by apply ndot_ne_disjoint.
        }
        assert (↑rpcRequestInvN {| Req_CID := cid; Req_Seq := seqno |} ## (↑eeN:coPset)).
        {
          apply ndot_preserve_disjoint_l.
          by apply ndot_ne_disjoint.
        }
        set_solver.
      }
      { simpl. done. }
      iDestruct "HH" as "(Hpre & Hupd & Hproc)".
      iDestruct "Hupd" as "[Hupd >Hlc]".
      iMod (lc_fupd_elim_later with "Hlc Hupd") as "Hupd".
      iNamed "Hupd".
      iMod "Hupd".
      iModIntro.
      iDestruct "Hupd" as (?) "[Hoplog2 Hupd]".
      iExists _.
      iFrame.
      iIntros "Hpblog".
      iDestruct (own_valid_2 with "Hlog Hoplog2") as %Hvalid.
      rewrite mono_list_auth_dfrac_op_valid_L in Hvalid.
      destruct Hvalid as [_ ->].
      iCombine "Hlog Hoplog2" as "Hoplog".
      iMod (own_update with "Hoplog") as "Hoplog".
      {
        apply mono_list_update.
        instantiate (1:=oldops ++ [lowop]).
        by apply prefix_app_r.
      }
      iDestruct "Hoplog" as "[Hoplog Hoplog2]".
      iMod ("Hupd" with "Hoplog2") as "Hupd".

      iMod (server_completes_request _ _ _ with "Herpc_inv Hreq Hpre [Hupd] Hproc") as "[#Hreceipt HerpcServer]".
      {
        apply subseteq_difference_r.
        { by apply ndot_ne_disjoint. }
        apply subseteq_difference_r.
        { by apply ndot_ne_disjoint. }
        set_solver.
      }
      { 
        apply subseteq_difference_r.
        {
          apply ndot_preserve_disjoint_l.
          by apply ndot_ne_disjoint. }
        apply subseteq_difference_r.
        {
          apply ndot_preserve_disjoint_l.
          by apply ndot_ne_disjoint. }
        set_solver.
      }
      { simpl. done. }
      {
        done.
      }
      simpl.
      iMod ("Hclose" with "[HerpcServer Hpblog Hoplog Hcids]").
      {
        iNext.
        iExists _; iFrame.
        rewrite compute_state_snoc.
        replace (compute_state ops) with (st) by done.
        rewrite X.
        rewrite /apply_op.
        simpl.
        rewrite decide_False; last first.
        { word. }
        iFrame.
      }
      iModIntro.
      (* finish up *)
      iIntros (?) "Hrep_sl _ Hpbck".
      iNamed 1.
      iMod (get_request_post with "Hreq Hreceipt Htok") as "HΦ".
      { done. }
      iMod (lc_fupd_elim_later with "Hlc2 HΦ") as "HΦ".
      iApply ("HΦ" with "[Herpc Hcid Hpbck Hseq] [Hrep_sl]").
      {
        repeat iExists _.
        iFrame "∗#".
        iPureIntro.
        word.
      }
      {
        rewrite /compute_reply.
        replace (compute_state ops) with (st) by done.
        rewrite X.
        rewrite /apply_op.
        simpl.
        rewrite decide_False; last first.
        { word. }
        done.
      }
    }
    { (* case: request already ran *)
      assert (int.nat (default (U64 0) (g !! cid)) = int.nat seqno ∨
                int.nat (default (U64 0) (g !! cid)) > int.nat seqno) as [Hok|HStale] by word.
      { (* case: not stale *)
        destruct (g !! cid) eqn:X2; last first.
        {
          exfalso.
          simpl in Hok.
          replace (int.nat 0%Z) with (0) in Hok by word.
          word.
        }
        iMod (server_replies_to_request _ {| Req_CID := cid ; Req_Seq:= _|} with "Herpc_inv HerpcServer") as "HH".
        {
          apply subseteq_difference_r.
          { by apply ndot_ne_disjoint. }
          apply subseteq_difference_r.
          { by apply ndot_ne_disjoint. }
          set_solver.
        }
        { simpl. rewrite X2. done. }
        { exists []. done. }
        iDestruct "HH" as "[#Hreceipt HerpcServer]".
        iExists _; iFrame.
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros "Hmask".
        iIntros "Hpblog".
        iMod "Hmask".

        iMod ("Hclose" with "[HerpcServer Hpblog Hlog Hcids]").
        {
          iNext.
          iExists _; iFrame.
          rewrite compute_state_snoc.
          replace (compute_state ops) with (st) by done.
          rewrite X.
          rewrite /apply_op.
          simpl.
          rewrite decide_True; last first.
          { rewrite -Hok. rewrite X2. word. }
          iFrame.
        }

        iModIntro.
        (* finish up *)
        iIntros (?) "Hrep_sl _ Hpbck".
        iNamed 1.
        replace (u0) with (seqno); last first.
        {
          simpl in Hok.
          word.
        }
        iMod (get_request_post with "Hreq Hreceipt Htok") as "HΦ".
        { done. }
        iMod (lc_fupd_elim_later with "Hlc2 HΦ") as "HΦ".
        iApply ("HΦ" with "[Herpc Hcid Hpbck Hseq] [Hrep_sl]").
        {
          repeat iExists _.
          iFrame "∗#".
          iPureIntro. word.
        }
        {
          simpl.
          rewrite /compute_reply.
          replace (compute_state ops) with (st) by done.
          rewrite X.
          rewrite /apply_op.
          simpl.
          rewrite decide_True; last first.
          { rewrite -Hok. rewrite X2. word. }
          done.
        }
      }
      { (* case: stale *)

        destruct (g !! cid) eqn:X2; last first.
        {
          exfalso.
          simpl in HStale.
          replace (int.nat 0%Z) with (0) in HStale by word.
          word.
        }
        iMod (smaller_seqno_stale_fact _ {| Req_CID := cid; Req_Seq := seqno |} with "Herpc_inv HerpcServer") as "HH".
        {
          apply subseteq_difference_r.
          { by apply ndot_ne_disjoint. }
          apply subseteq_difference_r.
          { by apply ndot_ne_disjoint. }
          set_solver.
        }
        { done. }
        { simpl in HStale.
          simpl.
          word. }
        iDestruct "HH" as "[HerpcServer #Hstale]".
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros "Hmask".
        iExists _; iFrame.
        iIntros "Hpblog".
        iMod "Hmask".
        iMod ("Hclose" with "[HerpcServer Hpblog Hlog Hcids]").
        {
          iNext. iExists _; iFrame.
          rewrite compute_state_snoc.
          replace (compute_state ops) with (st) by done.
          rewrite X.
          rewrite /apply_op.
          simpl.
          rewrite decide_True; last first.
          { rewrite X2. word. }
          iFrame.
        }
        iModIntro.
        iIntros (?) "Hsl _ Hpb".
        iNamed 1.
        iDestruct (client_stale_seqno with "Hstale Herpc") as %Hstale2.
        exfalso.
        simpl in Hstale2.
        word.
      }
    }
  }
Qed.

Definition own_StateMachine (s:loc) (ops:list eeOp) : iProp Σ :=
  let st := (compute_state ops) in
  match st with
  | ees nextCID lastSeq lastReply lowops =>
      ∃ (lastSeq_ptr lastReply_ptr lowSm:loc) own_low,
  "HnextCID" ∷ s ↦[EEStateMachine :: "nextCID"] #nextCID ∗
  "HlastSeq_ptr" ∷ s ↦[EEStateMachine :: "lastSeq"] #lastSeq_ptr ∗
  "HlastReply_ptr" ∷ s ↦[EEStateMachine :: "lastReply"] #lastReply_ptr ∗
  "HlastSeq" ∷ is_map lastSeq_ptr 1 lastSeq ∗
  "HlastReply" ∷ own_byte_map lastReply_ptr lastReply ∗

  "Hsm" ∷ s ↦[EEStateMachine :: "sm"] #lowSm ∗
  "#Hislow" ∷ low_is_InMemoryStateMachine lowSm own_low ∗
  "Hlowstate" ∷ own_low lowops
end
.

Notation ee_is_InMemory_applyVolatileFn := (is_InMemory_applyVolatileFn (sm_record:=ee_record)).
Notation ee_is_InMemory_setStateFn := (is_InMemory_setStateFn (sm_record:=ee_record)).
Notation ee_is_InMemory_getStateFn := (is_InMemory_getStateFn (sm_record:=ee_record)).

Lemma wp_EEStateMachine__apply s :
  {{{
        True
  }}}
    EEStateMachine__applyVolatile #s
  {{{
        applyFn, RET applyFn;
        ⌜val_ty applyFn (slice.T byteT -> slice.T byteT)⌝ ∗
        ee_is_InMemory_applyVolatileFn applyFn (own_StateMachine s)
  }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  iModIntro.
  iApply "HΦ".
  clear Φ.
  iSplit.
  {
    iPureIntro. econstructor.
  }
  iIntros (???? Φ) "!# Hpre HΦ".
  iDestruct "Hpre" as "(%Henc & #Hsl & Hown)".
  unfold own_StateMachine.
  set (st:=compute_state ops).
  destruct st eqn:X.
  iNamed "Hown".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (ret) "Hret".
  wp_pures.
  destruct op.
  { (* case: getcid op *)
    rewrite Henc.
    iMod (readonly_load with "Hsl") as (?) "Hsl2".
    wp_apply (wp_SliceGet with "[$Hsl2]").
    { done. }
    iIntros "Hsl2".
    wp_pures.
    wp_apply (wp_NewSliceWithCap).
    { word. }
    iIntros (?) "Hrep_sl".
    wp_store.
    wp_loadField.
    wp_load.
    wp_apply (wp_WriteInt with "[$Hrep_sl]").
    iIntros (?) "Hrep_sl".
    wp_store.
    wp_loadField.
    wp_storeField.
    wp_load.
    iApply "HΦ".
    rewrite compute_state_snoc.
    simpl.
    unfold apply_op.
    unfold compute_reply.
    replace (compute_state ops) with (st) by done.
    rewrite X.
    simpl.
    iModIntro.
    iSplitR "Hrep_sl"; last first.
    {
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iFrame.
    }
    iExists _, _, _, _.
    iFrame "Hislow ∗#".
  }
  { (* case: apply an op *)
    destruct Henc as [? [HlowEnc Henc]].
    rewrite Henc.
    iMod (readonly_load with "Hsl") as (?) "Hsl2".
    wp_apply (wp_SliceGet with "[$Hsl2]").
    { done. }
    iIntros "Hsl2".
    wp_pures.
    wp_apply (wp_SliceGet with "[$Hsl2]").
    { done. }
    iIntros "Hsl2".
    wp_pures.
    wp_apply (wp_slice_len).
    wp_pures.

    iDestruct (is_slice_small_sz with "Hsl2") as %Hsl_sz.
    wp_apply (wp_SliceSubslice_small with "[$Hsl2]").
    { rewrite -Hsl_sz.
      split; last done.
      rewrite app_length.
      simpl.
      word.
    }
    iIntros (eeop_sl) "Hop_sl".
    rewrite -Hsl_sz -Henc.
    rewrite -> subslice_drop_take; last first.
    { rewrite Henc. rewrite app_length. simpl. word. }
    rewrite Henc.
    rewrite app_length.
    rewrite singleton_length.
    replace (1 + length (u64_le u0 ++ u64_le u1 ++ x) - int.nat 1%Z)
      with (length (u64_le u0 ++ u64_le u1 ++ x)) by word.
    replace (int.nat (U64 1)) with (length [U8 0]) by done.
    rewrite drop_app.
    rewrite take_ge; last word.
    rename x into eeop_bytes.
    wp_pures.
    wp_apply (wp_ReadInt with "Hop_sl").
    iIntros (?) "Hop_sl".
    wp_apply (wp_ReadInt with "Hop_sl").
    iIntros (?) "Hop_sl".
    wp_pures.
    wp_loadField.
    wp_apply (wp_MapGet with "HlastSeq").
    iIntros (??) "(%Hlookup & HlastSeq)".
    wp_pures.
    wp_if_destruct.
    {
      wp_loadField.
      wp_apply (wp_byteMapGet with "HlastReply").
      iIntros (?) "[#Hrep_sl HlastReply]".
      wp_store.
      wp_pures.
      wp_load.
      iMod (readonly_load with "Hrep_sl") as (?) "Hrep_sl2".
      iModIntro.
      iApply "HΦ".

      rewrite compute_state_snoc.
      unfold apply_op.
      simpl.
      unfold compute_reply.
      replace (compute_state ops) with (st) by done.
      rewrite X.

      unfold apply_op_and_get_reply.
      rewrite decide_True; last first.
      {
        apply (f_equal fst) in Hlookup.
        rewrite map_get_val /= in Hlookup.
        rewrite Hlookup.
        word.
      }
      iSplitR "Hrep_sl2"; last first.
      {
        iClear "Hsl".
        iFrame.
      }
      simpl.
      iExists _, _, _, _.
      iFrame "Hislow ∗#".
    }
    {
      wp_loadField.
      iAssert (_) with "Hislow" as "#Hislow2".
      iNamed "Hislow2".
      wp_loadField.

      iMod (readonly_alloc (is_slice_small s'0 byteT 1 eeop_bytes) with "[Hop_sl]") as "#Hop_sl".
      { simpl. iFrame. }
      wp_apply ("HapplyVolatile_spec" with "[$Hlowstate]").
      {
        iSplitL; first done.
        iFrame "#".
      }
      iIntros (??) "[Hlowstate Hrep_sl]".
      wp_store.
      wp_pures.
      wp_load.

      iMod (readonly_alloc (is_slice_small reply_sl byteT 1 (low_compute_reply l p)) with "[Hrep_sl]") as "#Hreply_sl".
      { simpl. iFrame. }
      wp_loadField.
      iMod (readonly_load with "Hreply_sl") as (?) "Hreply_sl2".
      wp_apply (wp_byteMapPut with "[$HlastReply Hreply_sl2]").
      { iFrame. }
      iIntros "Hmap".
      wp_pures.
      wp_loadField.
      wp_apply (wp_MapInsert with "HlastSeq").
      { done. }
      iIntros "HlastSeq".
      wp_pures.
      wp_load.

      iMod (readonly_load with "Hreply_sl") as (?) "Hreply_sl2".
      iApply "HΦ".
      iModIntro.

      rewrite compute_state_snoc.
      unfold apply_op.
      simpl.
      unfold compute_reply.
      replace (compute_state ops) with (st) by done.
      rewrite X.

      unfold apply_op_and_get_reply.
      rewrite decide_False; last first.
      {
        apply (f_equal fst) in Hlookup.
        rewrite map_get_val /= in Hlookup.
        rewrite Hlookup.
        word.
      }
      iSplitR "Hreply_sl2"; last first.
      {
        iClear "Hsl".
        iFrame.
      }
      simpl.
      iExists _, _, _, _.
      iFrame "∗#".
    }
  }
Qed.

Lemma wp_EEStateMachine__setState s :
  {{{
        True
  }}}
    EEStateMachine__setState #s
  {{{
        setFn, RET setFn;
        ⌜val_ty setFn (slice.T byteT -> unitT)⌝ ∗
        ee_is_InMemory_setStateFn setFn (own_StateMachine s)
  }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  iModIntro.
  iApply "HΦ".
  clear Φ.
  iSplit.
  {
    iPureIntro. econstructor.
  }

  iIntros (???? Φ) "!# Hpre HΦ".
  iDestruct "Hpre" as "(%Hsnap & #Hsnap_sl & Hown)".
  wp_pures.

  iNamed "Hown".
  iMod (readonly_load with "Hsnap_sl") as (?) "Hsnap_sl2".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_load.
  simpl in Hsnap.
  unfold own_StateMachine.
  rewrite /ee_has_snap_encoding in Hsnap.
  set (st:=compute_state ops) in *.
  set (st_old:=compute_state ops_prev) in *.
  destruct st.
  destruct st_old.
  iNamed "Hown".
  destruct Hsnap as (lowsnap & enc_lastSeq & enc_lastReply & Hencseq  & Hencrep & Hlowsnap & Hsnap).
  rewrite Hsnap.
  wp_apply (wp_ReadInt with "[$Hsnap_sl2]").
  iIntros (?) "Hsnap_sl2".
  wp_pures.
  wp_storeField.
  wp_store.
  wp_load.

  wp_apply (wp_DecodeMapU64ToU64 with "[Hsnap_sl2]").
  {
    iSplitR; first done.
    iFrame.
  }
  iIntros (???) "[HlastSeqMap Hsnap_sl2]".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_load.
  wp_apply (wp_DecodeMapU64ToBytes with "[Hsnap_sl2]").
  {
    iSplitR; first done.
    iFrame.
  }
  iIntros (???) "[HlastReplyMap Hsnap_sl2]".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_load.
  wp_loadField.
  iAssert (_) with "Hislow" as "#Hislow2".
  iNamed "Hislow2".
  wp_loadField.
  iMod (readonly_alloc (is_slice_small rest_enc_sl0 byteT 1 lowsnap) with "[Hsnap_sl2]") as "#Hsnap_sl2".
  { simpl. iFrame. }
  wp_apply ("HsetState_spec" with "[$Hlowstate Hsnap_sl2]").
  {
    iSplitL; first done.
    iFrame "#".
  }
  iIntros "Hlowstate".
  wp_pures.
  iApply "HΦ".
  iExists _, _, _, _.
  iFrame "∗ Hislow".
  done.
Qed.

Lemma wp_EEStatemachine__getState (s:loc) :
  ⊢ ee_is_InMemory_getStateFn (λ: <>, EEStateMachine__getState #s) (own_StateMachine s).
Proof.
  iIntros (? Φ) "!# Hpre HΦ".
  iDestruct "Hpre" as "Hown".
  wp_pures.
  wp_call.
  unfold own_StateMachine.
  set (st:=compute_state ops).
  destruct st eqn:X.
  iNamed "Hown".
  wp_loadField.
  iAssert (_) with "Hislow" as "#Hislow2".
  iNamed "Hislow2".
  wp_loadField.
  wp_apply ("HgetState_spec" with "[$Hlowstate]").
  iIntros (??) "(Hlowstate & %Hlowsnap & #Hsnap_sl)".
  iMod (readonly_load with "Hsnap_sl") as (?) "Hsnap_sl2".
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { word. }
  iIntros (?) "Henc_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_loadField.
  wp_load.
  rewrite replicate_0.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_pures.
  wp_store.
  wp_loadField.
  wp_apply (wp_EncodeMapU64ToU64 with "HlastSeq").
  iIntros (??) "(Hmap & HlastSeqEnc & %HlastSeqEnc)".
  wp_load.
  iDestruct (is_slice_to_small with "HlastSeqEnc") as "HlastSeqEnc".
  wp_apply (wp_WriteBytes with "[$Henc_sl $HlastSeqEnc]").
  iIntros (?) "[Henc_sl _]".
  wp_store.
  wp_loadField.

  wp_apply (wp_EncodeMapU64ToBytes with "HlastReply").
  iIntros (??) "(Hmap2 & HlastReplyEnc & %HlastReplyEnc)".
  wp_load.
  iDestruct (is_slice_to_small with "HlastReplyEnc") as "HlastReplyEnc".
  wp_apply (wp_WriteBytes with "[$Henc_sl $HlastReplyEnc]").
  iIntros (?) "[Henc_sl _]".
  wp_store.
  wp_load.

  wp_apply (wp_WriteBytes with "[$Henc_sl $Hsnap_sl2]").
  iIntros (?) "[Henc_sl _]".
  wp_store.
  wp_load.
  iApply "HΦ".
  iDestruct (is_slice_to_small with "Henc_sl") as "Henc_sl".
  iMod (readonly_alloc_1 with "Henc_sl") as "Henc_sl".
  iModIntro.
  iFrame "Henc_sl".
  iSplitL.
  {
    repeat iExists _.
    iFrame "Hislow ∗#".
  }
  iPureIntro.
  cbn.
  unfold ee_has_snap_encoding.
  replace (compute_state ops) with (st) by done.
  rewrite X.
  exists snap, enc, enc0.
  split; first done.
  split; first done.
  split; first done.
  repeat rewrite -app_assoc.
  done.
Qed.

Lemma wp_MakeEEKVStateMachine own_low lowSm :
  {{{
        "#Hislow" ∷ low_is_InMemoryStateMachine lowSm own_low ∗
        "Hlowstate" ∷ own_low []
  }}}
    MakeEEKVStateMachine #lowSm
  {{{
      sm own_MemStateMachine, RET #sm;
        ee_is_InMemoryStateMachine sm own_MemStateMachine ∗
        own_MemStateMachine []
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_lam.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (?) "Hl".
  wp_pures.
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  wp_apply (wp_NewMap).
  iIntros (lastSeq_ptr) "HlastSeq".
  wp_storeField.
  wp_apply (wp_byteMapNew).
  iIntros (lastReply_ptr) "HlastReply".
  wp_storeField.
  wp_storeField.
  wp_storeField.

  wp_apply wp_EEStateMachine__apply.
  iIntros (?) "[% #Hisapply]".
  wp_apply wp_EEStateMachine__setState.
  iIntros (?) "[% #Hissetstae]".
  iApply wp_fupd.
  wp_apply wp_allocStruct.
  { repeat econstructor; done. }
  iIntros (?) "HH".
  iDestruct (struct_fields_split with "HH") as "HH".
  iNamed "HH".
  iMod (readonly_alloc_1 with "ApplyVolatile") as "#?".
  iMod (readonly_alloc_1 with "GetState") as "#?".
  iMod (readonly_alloc_1 with "SetState") as "#?".
  iApply "HΦ".
  iSplitR.
  {
    iExists _, _, _.
    iFrame "#".
    iModIntro.
    iApply wp_EEStatemachine__getState.
  }
  iNamed "Hpre".
  iModIntro.
  repeat iExists _.
  iFrame "∗#".
Qed.

Lemma wp_MakeClerk confHost γpblog γsys γoplog γerpc :
  {{{
    "#His_inv" ∷ is_inv γpblog γsys ∗
    "#Hee_inv" ∷ is_ee_inv γpblog γoplog γerpc ∗
    "#Herpc_inv" ∷ is_eRPCServer γerpc ∗
    "#Hconf" ∷ admin_proof.is_conf_host confHost γsys
  }}}
    eesm.MakeClerk #confHost
  {{{
        ck, RET #ck; own_Clerk ck γoplog
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_allocStruct).
  { repeat constructor. }
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply wp_MakeClerk.
  { iFrame "#". }
  iIntros (?) "Hck".
  wp_storeField.
  wp_apply (wp_NewSlice).
  iIntros (?) "Hsl".
  wp_pures.
  iDestruct (is_slice_to_small with "Hsl") as "Hsl".
  wp_apply (wp_SliceSet with "[$Hsl]").
  {
    simpl.
    iPureIntro.
    done.
  }
  iIntros "Hsl".
  wp_pures.
  wp_loadField.
  wp_bind (Clerk__Apply _ _).
  wp_apply (wp_frame_wand with "[-Hsl Hck]").
  { iNamedAccu. }
  wp_apply (wp_Clerk__Apply with "Hck [$Hsl]").
  {
    simpl.
    instantiate (1:=getcid).
    done.
  }
  iModIntro.

  iInv "Hee_inv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "[>Hpblog Hee]".
  set (st:=compute_state ops).
  destruct st eqn:X.
  iDestruct "Hee" as ">Hee".
  iNamed "Hee".
  iDestruct (big_sepS_elem_of_acc_impl u with "Hcids") as "[Hcid Hcids]".
  { set_solver. }
  iDestruct "Hcid" as "[%Hbad | Hcid]".
  { exfalso. word. }
  iExists _; iFrame.
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iIntros "Hpblog".
  iMod "Hmask".
  iMod ("Hclose" with "[HerpcServer Hpblog Hlog Hcids]").
  {
    iNext.
    iExists _; iFrame.
    rewrite compute_state_snoc.
    replace (compute_state ops) with (st) by done.
    rewrite X.
    rewrite /apply_op.
    simpl.
    iFrame.
    iApply "Hcids".
    {
      iModIntro.
      iIntros (???) "[%Hineq|$]".
      iLeft. iPureIntro.
      admit. (* FIXME: overflow inside the statemachine... *)
    }
    {
      iLeft.
      admit. (* FIXME: overflow inside the statemachine... *)
    }
  }
  iModIntro.
  iIntros (?) "Hrep_sl _ Hpbck".
  iNamed 1.
  wp_pures.
  wp_apply (wp_ReadInt with "[Hrep_sl]").
  {
    simpl.
    unfold compute_reply.
    replace (compute_state ops) with (st) by done.
    rewrite X.
    simpl.
    iFrame.
  }
  iIntros (?) "_".
  wp_pures.
  wp_storeField.
  wp_pures.
  wp_storeField.
  iApply "HΦ".
  iMod (readonly_alloc_1 with "ck") as "#?".
  iModIntro.
  repeat iExists _.
  iFrame "∗#%".
  iPureIntro.
  word.
Admitted.

End local_proof.
