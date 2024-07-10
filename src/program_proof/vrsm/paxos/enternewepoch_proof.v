From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require paxos.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial Require Export paxos.definitions paxos.withlock_proof.

Section enternewepoch_proof.

Context `{!heapGS Σ}.

Context `{!paxosG Σ}.
Context `{!paxosParams.t Σ}.
Import paxosParams.

Lemma wp_singleClerk__enterNewEpoch ck γ γsrv args_ptr args q :
  {{{
        "#His_ck" ∷ is_singleClerk ck γ γsrv ∗
        "Hargs" ∷ enterNewEpochArgs.own args_ptr args q
  }}}
    singleClerk__enterNewEpoch #ck #args_ptr
  {{{
        reply_ptr reply, RET #reply_ptr; enterNewEpochReply.own reply_ptr reply (DfracOwn 1) ∗
        if (decide (reply.(enterNewEpochReply.err) = (W64 0))) then
          enterNewEpoch_post γ γsrv reply args.(enterNewEpochArgs.epoch)
        else
          True
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (enterNewEpochArgs.wp_Encode with "Hargs").
  iIntros (enc enc_sl) "[%Hargs_enc Hsl]".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.
  iNamed "His_ck".
  wp_loadField.
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  iApply (wp_frame_wand with "[HΦ]").
  { iNamedAccu. }
  unfold is_paxos_host.
  iNamed "Hsrv".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Hsl Hrep").
  { iFrame "#". }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold enterNewEpoch_spec.
    iExists _.
    iSplitR; first done.
    simpl.
    iSplit.
    {
      iIntros (?) "Hpost".
      iIntros (?) "%Henc_reply Hsl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      rewrite Henc_reply.
      wp_apply (enterNewEpochReply.wp_Decode with "[$Hrep_sl]").
      { done. }
      iIntros (reply_ptr) "Hreply".
      iIntros "HΦ".
      iApply "HΦ".
      iFrame "∗".
      destruct (decide _).
      { iFrame. }
      done.
    }
    { (* Apply failed for some reason, e.g. node is not primary *)
      iIntros (? Hreply_err).
      iIntros (?) "%Henc_reply Hsl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      rewrite Henc_reply.
      wp_apply (enterNewEpochReply.wp_Decode with "[$Hrep_sl]").
      { done. }
      iIntros (reply_ptr) "Hreply".
      iIntros "HΦ".
      iApply "HΦ".
      iFrame "∗".
      destruct (decide _).
      { exfalso. done. }
      { done. }
    }
  }
  { (* RPC error *)
    iIntros.
    wp_pures.
    destruct (bool_decide _) as [] eqn:X.
    {
      exfalso.
      apply bool_decide_eq_true in X.
      naive_solver.
    }
    wp_pures.

    iDestruct (own_slice_small_nil byteT (DfracOwn 1) Slice.nil) as "Hsl".
    { done. }
    iMod (readonly_alloc_1 with "Hsl") as "#Hsl2".

    wp_apply (wp_allocStruct).
    { repeat econstructor. eauto. }
    iIntros (reply_ptr) "Hreply".
    iNamed 1.
    iApply "HΦ".
    iDestruct (struct_fields_split with "Hreply") as "HH".
    iNamed "HH".

    iSplitL.
    {
      iExists _.
      instantiate (1:=enterNewEpochReply.mkC _ _ _ _).
      simpl.
      replace (zero_val (slice.T byteT)) with (slice_val (Slice.nil)) by done.
      iFrame "∗#".
    }
    simpl.
    done.
  }
Qed.

Lemma wp_Server__enterNewEpoch (s:loc) (args_ptr reply_ptr:loc) γ γsrv args init_reply Φ Ψ :
  is_Server s γ γsrv -∗
  enterNewEpochArgs.own args_ptr args (DfracOwn 1) -∗
  enterNewEpochReply.own reply_ptr init_reply (DfracOwn 1) -∗
  (∀ reply, Ψ reply -∗ enterNewEpochReply.own reply_ptr reply (DfracOwn 1) -∗ Φ #()) -∗
  enterNewEpoch_core_spec γ γsrv args Ψ -∗
  WP Server__enterNewEpoch #s #args_ptr #reply_ptr {{ Φ }}
.
Proof.
  iIntros "#HisSrv Hpre Hreply HΦ HΨ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_Server__withLock with "[$]").
  iIntros (??) "HH".
  iNamed "HH".
  iNamed "Hvol".
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_pures.
  iNamed "HΨ".
  wp_if_destruct.
  { (* case: args.epoch ≤ s.epoch, do nothing *)
    iNamed "Hreply".
    wp_storeField.
    iModIntro.
    iExists _.
    repeat rewrite sep_exist_r.
    Opaque own_paxosState_ghost. iExists _; iFrame "∗#".
    iIntros "$ !#".
    Transparent own_paxosState_ghost.
    wp_pures.
    iRight in "HΨ".
    iApply ("HΦ" with "[HΨ]").
    2:{
      iExists _.
      instantiate (1:=enterNewEpochReply.mkC _ _ _ _).
      simpl.
      iFrame.
      done.
    }
    { iApply "HΨ". done. }
  }
  { (* case: args.epoch > s.epoch, can enter new epoch and return a vote *)
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_loadField.
    iNamed "Hreply".
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_loadField.
    wp_storeField.
    iModIntro. iExists _.
    rewrite sep_exist_r.
    instantiate (1:=paxosState.mk _ _ _ _ _).
    iExists _; simpl. iFrame "∗#".

    (* start ghost reasoning *)
    iIntros "Hghost". iNamed "Hghost".
    assert (uint.nat args.(enterNewEpochArgs.epoch) > uint.nat pst.(paxosState.epoch)) as Hineq by word.
    iDestruct (ghost_replica_helper1 with "Hghost") as "%HepochIneq".
    simpl in *.
    iMod (ghost_replica_enter_new_epoch with "Hghost") as "(Hghost & Htok & #Hrest)".
    { simpl. exact Hineq. }
    (* end ghost reasoning *)

    iModIntro.
    iSplitR "HΦ HΨ Hreply_err Hreply_acceptedEpoch Hreply_nextIndex Hreply_ret Hreply_ret_sl Htok".
    {
      repeat iExists _. simpl.
      iFrame "∗#". done.
    }

    wp_pures.
    iModIntro.
    iLeft in "HΨ".
    iSpecialize ("HΨ" with "[$Htok]").
    {
      instantiate (1:=enterNewEpochReply.mkC _ _ _ _).
      simpl.
      iExists _.
      iDestruct "Hrest" as "(Hacc & Hprop_lb & Hprop_facts)".
      simpl.
      iFrame "#".
      iPureIntro.
      split_and!; try done; word.
    }
    iApply ("HΦ" with "HΨ").
    iExists _.
    simpl.
    iFrame "∗#".
    rewrite HlogLen.
    iApply to_named.
    iExactEq "Hreply_nextIndex".
    repeat f_equal. word.
  }
Qed.

End enternewepoch_proof.
