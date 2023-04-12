From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Export pb_protocol.
From Perennial.program_proof.simplepb Require Import pb_marshal_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.simplepb Require Import pb_definitions.
From Perennial.program_proof.reconnectclient Require Import proof.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section pb_increasecommit_proof.
Context `{!heapGS Σ}.
Context {pb_record:Sm.t}.

Notation OpType := (Sm.OpType pb_record).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).
Notation own_Server_ghost_f := (own_Server_ghost_f (pb_record:=pb_record)).

Context `{!waitgroupG Σ}.
Context `{!pbG Σ}.

Lemma wp_Clerk__IncreaseCommit γ γsrv ck (epoch:u64) (newCommitIndex:u64) σ :
  {{{
        "#Hck" ∷ is_Clerk ck γ γsrv ∗
        "%HcommitLen" ∷ ⌜int.nat newCommitIndex = length σ⌝ ∗
        "#Hghost_epoch_lb" ∷ is_epoch_lb γsrv.(r_pb) epoch ∗
        "#Hcommit_by" ∷ committed_by γ.(s_pb) epoch σ ∗
        "#Hlog_lb" ∷ is_pb_log_lb γ.(s_pb) σ
  }}}
    Clerk__IncreaseCommitIndex #ck #newCommitIndex
  {{{ (err:u64), RET #err; True }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep) "Hrep".
  wp_pures.
  iNamed "Hck".
  wp_call.
  replace (slice.nil) with (slice_val Slice.nil) by done.
  wp_apply (wp_WriteInt with "[]").
  { iApply is_slice_zero. }
  iIntros (enc_args_sl) "Henc_args_sl".
  wp_loadField.
  iDestruct (is_slice_to_small with "Henc_args_sl") as "Henc_args_sl".
  wp_apply (wp_frame_wand with "HΦ").
  rewrite is_pb_host_unfold.
  iNamed "Hsrv".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Henc_args_sl Hrep").
  {
    iDestruct "Hsrv" as "(_ & _ & _ & _ & _ & _& $ & _)".
  }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold IncreaseCommit_spec.
    repeat iExists _.
    iSplitR; first done.
    simpl.
    unfold IncreaseCommit_core_spec.
    iFrame "#%".
    iIntros "_ %_ _ _ H".
    by iApply "H".
  }
  {
    iIntros (??) "_ _ H".
    by iApply "H".
  }
Qed.

(** Helper lemmas for GetState() server-side proof *)
Lemma increase_commitIndex_step γ γsrv st committedOps :
  no_overflow (length committedOps) →
  is_pb_log_lb γ.(s_pb) committedOps -∗
  is_proposal_lb γ.(s_pb) st.(server.epoch) committedOps -∗
  committed_by γ.(s_pb) st.(server.epoch) committedOps -∗
  own_Server_ghost_eph_f st γ γsrv
  ={↑pbN}=∗
  own_Server_ghost_eph_f (st <| server.committedNextIndex := length committedOps |> ) γ γsrv
.
Proof.
  iIntros (?) "#Hghost_lb #Hprop_lb #Hcomm_by".
  rewrite /own_Server_ghost_eph_f /tc_opaque /=.
  iNamed 1.
  rewrite /own_Primary_ghost_f /tc_opaque /=.
  iNamed "Hprimary".
  repeat iExists _; iFrame "Hghost_lb ∗ #".
  iPureIntro.
  split; first done.
  rewrite /get_rwops fmap_length /=.
  by unfold no_overflow in H.
Qed.

Lemma wp_Server__IncreaseCommit γ γsrv s args newCommitIndex Φ Ψ :
  is_Server s γ γsrv -∗
  (∀ reply, Ψ reply -∗ ∀ (reply_ptr:loc), GetStateReply.own reply_ptr reply -∗ Φ #reply_ptr) -∗
  IncreaseCommit_core_spec γ γsrv args.(GetStateArgs.epoch) epoch_lb Ψ -∗
  WP pb.Server__IncreaseCommitIndex #s #newCommitIndex {{ Φ }}
  .
Proof.
  iIntros "His_srv Hargs HΦ HΨ".
  wp_call.
  iNamed "His_srv".
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  iNamed "Hargs".
  wp_loadField.
  iNamed "Hvol".
  wp_loadField.
  wp_if_destruct.
  { (* reply with error *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat (iExists _).
      iSplitR "HghostEph"; last iFrame.
      repeat (iExists _).
      iFrame "∗#%".
    }
    unfold GetState_core_spec.
    iDestruct "HΨ" as "[_ HΨ]".
    iRight in "HΨ".
    wp_pures.
    iDestruct (is_slice_small_nil byteT 1 Slice.nil) as "#Hsl_nil".
    { done. }
    iMod (readonly_alloc_1 with "Hsl_nil") as "Hsl_nil2".
    wp_apply (wp_allocStruct).
    { Transparent slice.T. repeat econstructor.
      Opaque slice.T. }
    iIntros (reply_ptr) "Hreply".
    iDestruct (struct_fields_split with "Hreply") as "HH".
    iNamed "HH".
    iApply ("HΦ" with "[HΨ]"); last first.
    {
      iExists _. iFrame.
      instantiate (1:=GetStateReply.mkC _ _ _).
      replace (slice.nil) with (slice_val Slice.nil) by done.
      iFrame.
    }
    simpl.
    iApply "HΨ".
    done.
  }
  wp_storeField.
  wp_loadField.

  iDestruct (is_StateMachine_acc_getstate with "HisSm") as "HH".
  iNamed "HH".
  wp_loadField.
  iDestruct "HΨ" as "[#Hepoch_lb HΨ]".
  iDestruct (getstate_eph with "HghostEph") as "HghostEph".
  wp_apply ("HgetstateSpec" with "[$Hstate]").
  {
    iIntros "Hghost".
    iMod (getstate_step with "Hepoch_lb Hghost") as "[Hghost HH]".
    iFrame "Hghost".
    iModIntro.
    iExact "HH".
  }
  iIntros (??) "(#Hsnap_sl & %Hsnap_enc & [Hstate HQ])".
  iDestruct "HQ" as (?) "(%Hσeq_phys & #Hacc_ro &  #Hprop_lb & #Hprop_facts & #Hprim_facts & %Hepoch_ineq)".
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.

  iLeft in "HΨ".
  iDestruct ("HΨ" with "[% //] [%] Hacc_ro Hprop_facts Hprim_facts Hprop_lb [%] [%]") as "HΨ".
  { word. }
  { rewrite -Hσeq_phys. done. }
  { apply (f_equal length) in Hσeq_phys.
    unfold no_overflow in HnextIndexNoOverflow. (* FIXME: why manually unfold? *)
    word. }

  (* signal all opApplied condvars *)
  wp_apply (wp_MapIter with "HopAppliedConds_map HopAppliedConds_conds").
  { iFrame "HopAppliedConds_conds". }
  { (* prove one iteration of the map for loop *)
    iIntros.
    iIntros (?) "!# [_ #Hpre] HΦ".
    wp_pures.
    wp_apply (wp_condSignal with "Hpre").
    iApply "HΦ".
    iFrame "#".
    instantiate (1:=(λ _ _, True)%I).
    done.
  }
  iIntros "(HopAppliedConds_map & _ & _)".

  wp_pures.
  wp_apply (wp_NewMap).
  iIntros (opAppliedConds_loc_new) "Hmapnew".
  wp_storeField.
  wp_loadField.
  wp_apply (wp_condBroadcast with "[]").
  { done. }
  wp_loadField.
  wp_apply (release_spec with "[-Hsnap_sl HΨ HΦ]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    repeat (iExists _).
    iFrame "HghostEph".
    repeat (iExists _).
    iFrame "∗ HisSm #".
    iFrame "%".
    by iApply big_sepM_empty.
  }
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor.
    Opaque slice.T. }
  iIntros (reply_ptr) "Hreply".
  iDestruct (struct_fields_split with "Hreply") as "HH".
  iNamed "HH".
  iApply ("HΦ" with "HΨ").
  iExists _.
  iFrame.
  simpl.

  apply (f_equal length) in Hσeq_phys.
  rewrite Hσeq_phys.
  iFrame "∗#".
Qed.

End pb_increasecommit_proof.
