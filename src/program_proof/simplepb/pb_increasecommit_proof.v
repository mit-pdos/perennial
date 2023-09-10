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
Context {params:pbParams.t}.
Import pbParams.

Notation OpType := (Sm.OpType pb_record).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).

Context `{!waitgroupG Σ}.
Context `{!pbG Σ}.

Lemma wp_Clerk__IncreaseCommit γ γsrv ck (epoch:u64) (newCommitIndex:u64) σ :
  {{{
        "#Hck" ∷ is_Clerk ck γ γsrv ∗
        "%HcommitLen" ∷ ⌜int.nat newCommitIndex = length σ⌝ ∗
        "#Hghost_epoch_lb" ∷ is_epoch_lb γsrv.(r_pb) epoch ∗
        "#Hcomm_fact" ∷ □committed_log_fact γ epoch σ ∗
        "#Hlog_lb" ∷ is_pb_log_lb γ.(s_pb) σ ∗
        "#Hprop_lb" ∷ is_proposal_lb γ.(s_pb) epoch σ
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
  { iApply own_slice_zero. }
  iIntros (enc_args_sl) "Henc_args_sl".
  wp_loadField.
  iDestruct (own_slice_to_small with "Henc_args_sl") as "Henc_args_sl".
  wp_apply (wp_frame_wand with "HΦ").
  rewrite is_pb_rpcs_unfold.
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
    iExists _, _.
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

Lemma getEpoch_ineq γ γsrv st epoch {own_StateMachine} :
  is_epoch_lb γsrv.(r_pb) epoch -∗
  £ 1 -∗
  accessP_fact own_StateMachine (own_Server_ghost_f γ γsrv) -∗
  own_StateMachine st.(server.epoch) (get_rwops st.(server.ops_full_eph)) st.(server.sealed) (own_Server_ghost_f γ γsrv) -∗
  |NC={⊤}=>
  own_StateMachine st.(server.epoch) (get_rwops st.(server.ops_full_eph)) st.(server.sealed) (own_Server_ghost_f γ γsrv) ∗
  ⌜int.nat epoch <= int.nat st.(server.epoch)⌝
.
Proof.
  iIntros "#? Hlc HaccP Hstate".
  iMod ("HaccP" with "Hlc [] Hstate") as "$"; last done.
  iIntros (???).
  iNamed 1.
  iDestruct (ghost_epoch_lb_ineq with "[$] Hghost") as %?.
  iModIntro.
  iFrame "%". repeat iExists _; iFrame "∗#%".
Qed.

Lemma increase_commitIndex_step γ γsrv st epoch committedOps :
  int.nat (length committedOps) >= int.nat st.(server.committedNextIndex) →
  int.nat (length committedOps) <= length st.(server.ops_full_eph) →
  int.nat epoch <= int.nat st.(server.epoch) →
  no_overflow (length committedOps) →
  is_pb_log_lb γ.(s_pb) committedOps -∗
  is_proposal_lb γ.(s_pb) epoch committedOps -∗
  □ committed_log_fact γ epoch committedOps -∗
  own_Server_ghost_eph_f st γ γsrv
  -∗
  own_Server_ghost_eph_f (st <| server.committedNextIndex := length committedOps |> ) γ γsrv
.
Proof.
  iIntros (????) "#Hghost_lb #Hprop_lb #Hcomm_fact_in".
  rewrite /own_Server_ghost_eph_f /tc_opaque /=.
  iNamed 1.
  rewrite /own_Primary_ghost_f /tc_opaque /=.
  iNamed "Hprimary".
  iExists committedOps. iFrame "Hghost_lb ∗ #".
  iSplitL.
  {
    iModIntro.
    iIntros (?). iIntros.
    iApply "Hcomm_fact_in".
    { iPureIntro. instantiate (1:=epoch'). word. }
    { iPureIntro. destruct H4; first word.
      word. }
    { iFrame "#". }
    { iFrame "#". }
  }
  iSplitL.
  {
    iDestruct ("Hcomm_fact_in" with "[//] [] [] Hs_prop_facts") as %?.
    { iPureIntro. unfold no_overflow in *. word. }
    { iFrame "#". }
    by iDestruct (fmlist_ptsto_lb_mono with "Hs_prop_lb") as "$".
  }
  iPureIntro.
  rewrite /get_rwops fmap_length /=.
  by unfold no_overflow in H.
Qed.

Lemma wp_Server__IncreaseCommit γ γsrv s newCommitIndex Φ Ψ :
  is_Server s γ γsrv -∗
  (Ψ () -∗ Φ #()) -∗
  IncreaseCommit_core_spec γ γsrv newCommitIndex Ψ -∗
  WP pb.Server__IncreaseCommitIndex #s #newCommitIndex {{ Φ }}
  .
Proof.
  iIntros "His_srv HΦ HΨ".
  wp_call.
  iNamed "His_srv".
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pure1_credit "Hlc".
  iNamed "Hvol".
  wp_loadField.
  iDestruct "HΨ" as (??) "(% & #? & #? & #? & #? & HΨ)".
  iMod (getEpoch_ineq with "[$] Hlc [] Hstate") as "(Hstate & %)".
  {
    rewrite /is_StateMachine /tc_opaque.
    by iNamed "HisSm".
  }
  wp_apply (wp_and with "[HnextIndex]").
  { iNamedAccu. }
  { wp_pures. done. }
  { iIntros (?). iNamed 1. wp_loadField. wp_pures. iFrame. done. }
  iNamed 1.
  wp_if_destruct.
  { (* increase commit index *)
    iDestruct (increase_commitIndex_step with "[$] [$] [$] HghostEph") as "HghostEph".
    { word. }
    { unfold no_overflow in *.
      rewrite fmap_length in HnextIndexNoOverflow Heqb.
      word. }
    { unfold no_overflow. word. }
    { unfold no_overflow. word. }
    wp_storeField.
    wp_loadField.
    wp_apply (wp_condBroadcast with "[]").
    { iFrame "#". }
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat (iExists _).
      iSplitR "HghostEph"; last iFrame.
      repeat (iExists _).
      iFrame "∗#%".
      simpl.
      rewrite -H.
      iApply to_named.
      iExactEq "HcommittedNextIndex".
      repeat f_equal. word.
    }
    wp_pures.
    by iApply "HΦ".
  }
  {
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "HmuInv Hlocked".
      iNext. repeat (iExists _).
      iSplitR "HghostEph"; last iFrame.
      repeat (iExists _). iFrame "∗#%".
    }
    wp_pures.
    by iApply "HΦ".
  }
Qed.

End pb_increasecommit_proof.
