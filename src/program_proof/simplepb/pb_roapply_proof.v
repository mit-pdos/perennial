From Perennial.base_logic Require Import lib.saved_prop.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_protocol.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb Require Import config_proof pb_definitions pb_marshal_proof.
(* FIXME: importing apply_proof for some lemmas *)
From Perennial.program_proof.reconnectclient Require Import proof.

Section pb_roapply_proof.

Context `{!heapGS Σ}.
Context {params:pbParams.t}.
Import pbParams.
Import Sm.

Context `{!pbG Σ}.

Lemma wp_Clerk__ApplyRo γ γsrv ck op_sl q op (op_bytes:list u8) (Φ:val → iProp Σ) :
has_op_encoding op_bytes op →
is_readonly_op op →
is_Clerk ck γ γsrv -∗
own_slice_small op_sl byteT q op_bytes -∗
□((|={⊤∖↑pbN,∅}=> ∃ ops, own_int_log γ ops ∗
  (own_int_log γ ops ={∅,⊤∖↑pbN}=∗
     □(∀ reply_sl, own_slice_small reply_sl byteT 1 (compute_reply ops op) -∗
            own_slice_small op_sl byteT q op_bytes -∗
                Φ (#(U64 0), slice_val reply_sl)%V)))
∗
(∀ (err:u64) unused_sl, ⌜err ≠ 0⌝ -∗ own_slice_small op_sl byteT q op_bytes -∗
                                     Φ (#err, (slice_val unused_sl))%V )) -∗
WP Clerk__ApplyRo #ck (slice_val op_sl) {{ Φ }}.
Proof.
  intros Henc Hro.
  iIntros "#Hck Hop_sl".
  iIntros "#HΦ".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep) "Hrep".
  wp_pures.
  iNamed "Hck".
  wp_loadField.
  rewrite is_pb_rpcs_unfold.
  iNamed "Hsrv".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Hop_sl Hrep").
  {
    iDestruct "Hsrv" as "(_ & _ & _ & _ & _ & $ & _)".
  }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold Apply_spec.
    iExists _.
    iSplitR; first done.
    iSplitR; first done.
    iSplit.
    {
      iModIntro.
      iLeft in "HΦ".
      iMod "HΦ".
      iModIntro.
      iDestruct "HΦ" as (?) "[Hlog HΦ]".
      iExists _.
      iFrame.
      iIntros "Hlog".
      iMod ("HΦ" with "Hlog") as "#HΦ".
      iModIntro.
      iModIntro.
      iIntros (? Hreply_enc) "Hop".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      rewrite Hreply_enc.
      wp_apply (ApplyReply.wp_Decode with "[Hrep_sl]").
      { iFrame. iPureIntro. done. }
      iIntros (reply_ptr) "Hreply".
      wp_pures.
      iNamed "Hreply".
      wp_loadField.
      wp_loadField.
      wp_pures.
      iModIntro.
      iApply ("HΦ" with "Hrepy_ret_sl Hop").
    }
    { (* Apply failed for some reason, e.g. node is not primary *)
      iIntros (??).
      iModIntro.
      iIntros (Herr_nz ? Hreply_enc) "Hop".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      iIntros.
      wp_pures.
      wp_load.
      wp_apply (ApplyReply.wp_Decode with "[$Hrep_sl]").
      { done. }
      iIntros (reply_ptr) "Hreply".
      iNamed "Hreply".
      wp_pures.
      wp_loadField.
      wp_loadField.
      iRight in "HΦ".
      wp_pures.
      iApply ("HΦ" with "[] Hop").
      done.
    }
  }
  { (* RPC error *)
    iIntros.
    wp_pures.
    wp_if_destruct.
    {
      wp_load.
      exfalso. done.
    }
    iRight in "HΦ".
    replace (slice.nil) with (slice_val Slice.nil) by done.
    wp_pures.
    iApply ("HΦ" with "[] [$]").
    done.
  }
Qed.

Lemma is_StateMachine_acc_applyReadonly sm own_StateMachine P :
  is_StateMachine sm own_StateMachine P -∗
  (∃ applyFn,
    "#Happly" ∷ readonly (sm ↦[pb.StateMachine :: "ApplyReadonly"] applyFn) ∗
    "#HapplySpec" ∷ is_ApplyReadonlyFn own_StateMachine applyFn P
  )
.
Proof.
  rewrite /is_StateMachine /tc_opaque.
  iNamed 1. iExists _; iFrame "#".
Qed.

Lemma own_int_log_agree γ ops ops' :
  own_int_log γ ops -∗
  own_int_log γ ops' -∗
  ⌜ops = ops'⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %?.
  iPureIntro.
  rewrite mono_list_auth_dfrac_op_valid_L in H.
  naive_solver.
Qed.

Lemma generate_read_fupd γ Φ rop :
  is_helping_inv γ -∗
  (|={⊤ ∖ ↑pbN,∅}=>
    ∃ ops, own_int_log γ ops ∗
      (own_int_log γ ops ={∅,⊤ ∖ ↑pbN}=∗ □ Φ (compute_reply ops rop))) -∗
  (|={⊤ ∖ ↑pbN ∪ ↑appN,∅}=>
    ∃ σ, own_pre_log γ.(s_prelog) σ ∗
      (own_pre_log γ.(s_prelog) σ ={∅,⊤ ∖ ↑pbN ∪ ↑appN}=∗ □ Φ (compute_reply (get_rwops σ) rop)))
.
Proof.
  iIntros "#Hinv Hupd".
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (?) "(Hghost & >Hlog & #HrwQs)".
  iMod (fupd_mask_subseteq (⊤∖↑pbN)) as "Hmask".
  { solve_ndisj. }
  iMod "Hupd" as (?) "[Hlog2 Hupd]".
  iDestruct (own_int_log_agree with "Hlog Hlog2") as %?; subst.
  iDestruct "Hghost" as (?) "(>Hghost & >% & Hprops)".
  iModIntro.
  iExists _; iFrame.
  iIntros "Hghost".
  iMod ("Hupd" with "Hlog2") as "#Hupd".
  unfold get_rwops.
  rewrite -H.
  iFrame "#".
  iMod "Hmask".
  iMod ("Hclose" with "[-]"); last done.
  iNext.
  iExists _.
  iFrame "∗#".
  rewrite H. iFrame.
  iExists _; iFrame "∗#%".
Qed.

Lemma preread_step st γ γsrv t (lastModifiedIndex:u64) Q rop {own_StateMachine} :
  st.(server.leaseValid) = true →
  int.nat t < int.nat st.(server.leaseExpiration) →
  (∀ σ', prefix σ' st.(server.ops_full_eph) →
         int.nat lastModifiedIndex <= length σ' → compute_reply (get_rwops σ') rop = compute_reply (get_rwops st.(server.ops_full_eph)) rop) →
  £ 1 -∗
  £ 1 -∗
  £ 1 -∗
  own_time t -∗
  □(|={⊤ ∖ ↑pbN ∪ ↑appN,∅}=>
    ∃ σ, own_pre_log γ.(s_prelog) σ ∗
      (own_pre_log γ.(s_prelog) σ ={∅,⊤ ∖ ↑pbN ∪ ↑appN}=∗ □ Q (compute_reply (get_rwops σ) rop))) -∗
  own_Server_ghost_eph_f st γ γsrv -∗
  accessP_fact own_StateMachine (own_Server_ghost_f γ γsrv) -∗
  own_StateMachine st.(server.epoch) (get_rwops st.(server.ops_full_eph)) st.(server.sealed) (own_Server_ghost_f γ γsrv) -∗
  is_repl_inv γ.(s_pb) -∗
  |NC={⊤}=>
  own_StateMachine st.(server.epoch) (get_rwops st.(server.ops_full_eph)) st.(server.sealed) (own_Server_ghost_f γ γsrv) ∗
  is_preread_inv γ.(s_pb) γ.(s_prelog) γ.(s_reads) ∗
  is_proposed_read γ.(s_reads) (int.nat lastModifiedIndex) (λ σ, Q (compute_reply (get_rwops σ) rop)) ∗
  is_proposal_lb γ.(s_pb) st.(server.epoch) st.(server.ops_full_eph) ∗
  own_time t ∗
  own_Server_ghost_eph_f st γ γsrv.
Proof.
  iIntros (?? HlastModified) "Hlc Hlc2 Hlc3 Htime #Hupd Hghost #HaccP Hstate #HpbInv".
  iEval (rewrite /own_Server_ghost_eph_f /tc_opaque) in "Hghost".
  iNamed "Hghost".
  iNamed "Hlease".
  rewrite H.
  iDestruct "Hlease" as (??) "(#HconfInv & #Hlease & #Hlease_lb)".

  (* Step 1. use accessP_fact to get ownership of locally accepted state *)
  iMod ("HaccP" with "Hlc [-Hstate] Hstate") as "$"; last done.
  iIntros (???) "Hghost".
  iClear "Hin_conf".
  iNamed "Hghost".

  iInv "HpbInv" as "Hown" "HclosePb".
  iMod (lc_fupd_elim_later with "Hlc3 Hown") as "Hown".
  iDestruct "Hown" as (??) "(Hcommit & #Haccs & #? & #?)".
  destruct (decide (int.nat st.(server.epoch) < int.nat epoch)).
  { (* case: something has been committed in a higher epoch than the
       server's.
       Will use the lease that we have on the epoch number together with the
       fact that configurations for higher epochs are undecided (according to
       is_conf_inv) to derive a contradiction.
     *)
    iMod (lease_acc with "Hlease_lb Hlease Htime") as "[>HleasedEpoch _]".
    { solve_ndisj. }
    { done. }
    iInv "HconfInv" as "Hown" "_".
    iMod (lc_fupd_elim_later with "Hlc2 Hown") as "Hown".
    iNamed "Hown".
    iDestruct (mono_nat_auth_own_agree with "Hepoch HleasedEpoch") as %HepochEq.
    subst.
    iDestruct "Haccs" as (?) "[#HsomeConf _]".
    iDestruct (mono_nat_auth_own_agree with "Hepoch HleasedEpoch") as %[_ Heq].
    assert (epoch0 = st.(server.epoch)) by word; subst.
    unfold is_epoch_config.
    iDestruct "HsomeConf" as "[HsomeConf _]".
    destruct (decide (int.nat reservedEpoch < int.nat epoch)).
    {
      iDestruct (big_sepS_elem_of_acc _ _ epoch with "Hunreserved") as "[HH _]".
      { set_solver. }
      iSpecialize ("HH" with "[%]").
      { word. }
      iDestruct "HH" as "(_ & Hunset & _)".
      iDestruct (own_valid_2 with "Hunset HsomeConf") as %Hbad.
      exfalso.
      rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hbad.
      by destruct Hbad as [Hbad _].
    }
    assert (int.nat reservedEpoch = int.nat epoch ∨ int.nat epoch < int.nat reservedEpoch) as [|] by word.
    { replace (reservedEpoch) with epoch by word.
      iDestruct "Hunset_or_set" as "[Hbad|%Hbad]"; last exfalso.
      2:{ word. }
      iDestruct (own_valid_2 with "Hbad HsomeConf") as %Hbad.
      exfalso.
      rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hbad.
      by destruct Hbad as [Hbad _].
    }
    {
      iSpecialize ("His_skip" $! epoch with "[%] [%]").
      { word. }
      { word. }
      iDestruct (own_valid_2 with "His_skip HsomeConf") as %Hbad.
      exfalso.
      rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hbad.
      by destruct Hbad as [_ Hbad].
    }
  }

  (* Given that last committed epoch <= server.epoch, prove that this server has
     all the ops that are committed.
     This involves using ownership of accepted state and knowledge that we are
     in the configuration.
   *)
  iAssert (⌜prefix σ st.(server.ops_full_eph)⌝)%I with "[-]" as "%".
  {
    destruct (decide (int.nat epoch < int.nat st.(server.epoch))).
    { (* case: nothing is committed in st.(server.epoch). In this case, we use
         old_prop_max. To conclude that the server has all the committed ops. *)
      iDestruct "Hs_prop_facts" as "[Hmax _]".
      iApply "Hmax".
      { iPureIntro; done. }
      iFrame "#".
    }
    { (* case: something committed in epoch. We are in that configuration, so we
         accepted that something. *)
      iDestruct "Hin_conf" as (?) "[#Hconf %Hin]".
      iDestruct "Haccs" as (?) "[#Hconf2 Haccs]".
      assert (epoch = st.(server.epoch)) by word; subst.
      iDestruct (is_epoch_conf_agree with "Hconf2 Hconf") as "%"; subst.
      iSpecialize ("Haccs" $! γsrv.(r_pb) with "[//]").
      iDestruct (ghost_accept_lb_ineq with "Haccs Hghost") as "%".
      iDestruct (ghost_get_proposal_facts with "Hghost") as "[#Hprop_lb _]".
      iDestruct (fmlist_ptsto_lb_comparable with "Hs_prop_lb Hprop_lb") as %[|].
      2: { iPureIntro. by transitivity opsfull. }
      { iPureIntro.
        apply list_prefix_eq in H3.
        2:{
          apply prefix_length in H1.
          by do 2 rewrite fmap_length in H1.
        }
        by subst.
      }
    }
  }

  iMod (start_read_step _ _ _ _ lastModifiedIndex (λ someσ, compute_reply (get_rwops someσ) rop)
         with "Hlc2 [$] [Hupd] Hcommit") as "[H Hcommit]".
  { solve_ndisj. }
  { intros.
    epose proof (HlastModified σ _ _) as ->.
    epose proof (HlastModified σ' _ _) as ->.
    done.
    Unshelve.
    2:{ etransitivity; done. }
    2:{ apply prefix_length in H3. word. }
    2:{ by etransitivity. }
    2:{ word. }
    shelve.
  }
  {
    iModIntro.
    iMod (fupd_mask_subseteq (⊤∖↑pbN ∪ ↑appN)) as "Hmask".
    {
      apply union_subseteq.
      split.
      { solve [eauto 20 with ndisj]. } (* FIXME: increase search depth? *)
      { solve_ndisj. }
    }
    iMod "Hupd" as (?) "[? Hupd]".
    iModIntro. iExists _; iFrame.
    iIntros "?". iMod ("Hupd" with "[$]").
    by iMod "Hmask".
  }
  iFrame "H".
  iMod ("HclosePb" with "[-Htime Hprimary Hghost Hprim_escrow]").
  { iNext; repeat iExists _; iFrame "∗#". }
  iModIntro.
  iFrame.
  iSplitR "Hprimary".
  { repeat iExists _; iFrame "∗#%". }
  iFrame "#".
  iEval (rewrite /own_Server_ghost_eph_f /tc_opaque).
  iFrame "∗#%".
  repeat iExists _; iFrame "∗#%".
  rewrite H.
  repeat iExists _; iFrame "∗#%".
Qed.

(* FIXME: move to pb_protocol *)
Lemma is_pb_log_lb_mono γ σ σ' :
  prefix σ σ' →
  is_pb_log_lb γ.(s_pb) σ' -∗
  is_pb_log_lb γ.(s_pb) σ.
Proof.
  iIntros (?) "?".
  iApply (own_mono with "[$]").
  by apply mono_list_lb_mono.
Qed.

Lemma roapply_finish_step st γ γsrv Q priorOps :
  int.nat st.(server.committedNextIndex) >= length priorOps →
  £ 1 -∗
  £ 1 -∗
  is_proposal_lb γ.(s_pb) st.(server.epoch) priorOps -∗
  is_proposed_read γ.(s_reads) (length priorOps) Q -∗
  is_preread_inv γ.(s_pb) γ.(s_prelog) γ.(s_reads) -∗
  own_Server_ghost_eph_f st γ γsrv ={⊤}=∗
  own_Server_ghost_eph_f st γ γsrv ∗
  Q priorOps
.
Proof.
  intros HcommitIndex.
  iIntros "Hlc Hlc2 #Hprop_lb #Hprop_read #HpreInv HghostEph".
  iEval (rewrite /own_Server_ghost_eph_f /tc_opaque) in "HghostEph".
  iNamed "HghostEph".
  iAssert (is_pb_log_lb γ.(s_pb) priorOps) with "[-]" as "#Hprior_commit_lb".
  {
    iDestruct (fmlist_ptsto_lb_comparable with "Hprop_lb Hcommit_prop_lb") as %[|].
    { by iApply is_pb_log_lb_mono. }
    apply list_prefix_eq in H.
    2:{
      rewrite fmap_length in HcommitLen.
      word.
    }
    by subst.
  }
  iMod (fupd_mask_subseteq (↑prereadN)) as "Hmask".
  { set_solver. }
  iMod (finish_read_step with "Hlc Hlc2 [$] [$] [$]") as "#H".
  { done. }
  iFrame "H".
  iMod "Hmask". iModIntro.
  repeat iExists _; iFrame "∗#%".
Qed.

Lemma wp_Server__ApplyRo (s:loc) γ γsrv op_sl op (enc_op:list u8) Ψ (Φ: val → iProp Σ) :
  is_Server s γ γsrv -∗
  readonly (own_slice_small op_sl byteT 1 enc_op) -∗
  (∀ reply, Ψ reply -∗ ∀ reply_ptr, ApplyReply.own_q reply_ptr reply -∗ Φ #reply_ptr) -∗
  ApplyRo_core_spec γ op enc_op Ψ -∗
  WP (pb.Server__ApplyRoWaitForCommit #s (slice_val op_sl)) {{ Φ }}
.
Proof.
  iIntros "#Hsrv #Hop_sl".
  iIntros "HΨ HΦ".
  iApply (wp_frame_wand with "HΨ").
  iDestruct "HΦ" as "(%Hop_enc & %Hro & #Hupd & #Hfail_Φ)".
  iNamed "Hsrv".
  rewrite /Server__ApplyRoWaitForCommit.
  wp_pure1_credit "Hlc1".
  wp_pure1_credit "Hlc2".
  wp_pure1_credit "Hlc3".
  wp_apply (wp_allocStruct).
  { eauto. }
  iIntros (reply_ptr) "Hreply".
  iDestruct (struct_fields_split with "Hreply") as "HH".
  iNamed "HH".
  wp_pure1_credit "Hlc4".
  wp_pures.
  simpl.
  replace (slice.nil) with (slice_val (Slice.nil)) by done.
  wp_storeField.
  wp_storeField.

  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  iNamed "Hvol".
  wp_pures.
  wp_loadField.
  wp_if_destruct.
  { (* lease invalid *)
    wp_loadField.
    wp_apply (release_spec with "[-Hlc1 Hlc2 Hlc3 Hupd Err Reply]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat iExists _; iFrame "HghostEph".
      repeat iExists _.
      iFrame "∗#%".
    }
    wp_pures. wp_storeField.
    iModIntro. iIntros "HΦ".
    iApply ("HΦ" $! (ApplyReply.mkC _ _)).
    2:{
      iExists _, 1%Qp; iFrame.
      by iApply own_slice_small_nil.
    }
    by iApply "Hfail_Φ".
  }

  wp_apply wp_RandomUint64.
  iIntros (rnd) "_".

  wp_apply (wp_If_join emp).
  { iSplit.
    - iIntros "_". wp_pures. done.
    - iIntros "_". wp_pures. done.
  }
  iIntros "_".

  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (lastModified) "HlastModified".
  wp_pures.
  iDestruct (is_StateMachine_acc_applyReadonly with "HisSm") as "H".
  iNamed "H".
  wp_loadField.
  wp_loadField.
  wp_apply ("HapplySpec" with "[$Hstate]").
  { iFrame "#%". }
  iIntros (???) "(%HlastModifiedLen & %HlastModified & Hrep_sl & Hstate)".
  wp_pures.
  wp_store.
  wp_storeField.
  wp_loadField.

  wp_apply wp_GetTimeRange.
  iIntros (?????) "Htime".
  destruct (decide (int.nat h < int.nat st.(server.leaseExpiration))).
  { (* case: got lease is not expired *)

    (* proof steps here:
       use accessP to get accepted ↦ σ, with (σ ⪯ ops).
       a
       Combine with
     *)
    iMod (preread_step _ _ _ _ lastModifiedIndex with "Hlc1 Hlc2 Hlc3 Htime [] HghostEph [] [Hstate] [$]") as "HH".
    { done. }
    { word. }
    { intros.
      epose proof (HlastModified _ _) as ->.
      1: done.
      by rewrite fmap_length.
    }
    { iModIntro. iApply generate_read_fupd.
      { iFrame "#". }
      {
        instantiate (1:=(λ b,
                          Ψ {| ApplyReply.err := 0; ApplyReply.ret := b |})
                    ).
        iFrame "#". }
    }
    {
      iClear "Happly HapplySpec".
      rewrite /is_StateMachine /tc_opaque.
      by iNamed "HisSm".
    }
    { iFrame. }
    iDestruct "HH" as "(Hstate & #Hpre_inv & #Hprop_read & #Hprop_lb & Htime & HghostEph)".
    iModIntro.
    iFrame "Htime".
    wp_pures.
    wp_loadField.
    wp_if_destruct.
    { exfalso. word. }
    wp_pures.

    iAssert (mu_inv s γ γsrv mu) with "[-Err Reply Hlocked Hrep_sl HlastModified]" as "Hown".
    {
      repeat iExists _; iSplitR "HghostEph"; last by iFrame.
      repeat iExists _; iFrame "∗#%".
    }
    wp_forBreak_cond.

    wp_pures.
    iNamed "Hown".
    iNamed "Hvol".
    wp_loadField.
    wp_pure1_credit "Hlc".
    wp_if_destruct.
    {
      wp_storeField.
      iRight.
      iModIntro. iSplitR; first done.
      wp_pures.
      wp_loadField.
      wp_apply (release_spec with "[-Err Reply Hrep_sl]").
      {
        iFrame "HmuInv Hlocked".
        iNext.
        repeat iExists _; iSplitR "HghostEph"; last by iFrame.
        repeat iExists _; iFrame "∗#%".
      }
      wp_pures.
      iModIntro.
      iIntros "HΦ".
      iApply ("HΦ" $! (ApplyReply.mkC _ _) with "[]").
      2:{
        iExists _, _. iFrame.
      }
      by iApply "Hfail_Φ".
    }
    wp_load.
    wp_loadField.
    wp_pure1_credit "Hlc2".
    wp_pures.
    wp_if_destruct.
    { (* the read is finished! *)
      wp_storeField.
      iRight.
      iMod (roapply_finish_step _ _ _ _ (take (int.nat lastModifiedIndex) st.(server.ops_full_eph))
             with "Hlc Hlc2 [] [Hprop_read] [] HghostEph") as "H".
      { rewrite fmap_length /no_overflow in Heqb2 HnextIndexNoOverflow.
        rewrite take_length. word. }
      { rewrite -Heqb1. iDestruct (fmlist_ptsto_lb_mono with "Hprop_lb") as "$".
        eexists (drop _ _). by setoid_rewrite take_drop.
      }
      {
        rewrite take_length_le; first iFrame "#".
        rewrite fmap_length in HlastModifiedLen.
        word.
      }
      { iFrame "#". }
      iDestruct "H" as "[HghostEph HΨ]".
      iModIntro. iSplitR; first done.
      wp_pures.
      wp_loadField.
      wp_apply (release_spec with "[-HΨ Err Reply Hrep_sl]").
      {
        iFrame "HmuInv Hlocked".
        iNext.
        repeat iExists _; iSplitR "HghostEph"; last by iFrame.
        repeat iExists _; iFrame "∗#%".
      }
      wp_pures.
      iModIntro.
      iIntros "HΦ".
      iApply ("HΦ" with "[$]").
      repeat iExists _; iFrame.
      simpl.
      iApply to_named.
      iExactEq "Hrep_sl".
      f_equal.
      epose proof (HlastModified _ _) as ->.
      { done. }
      { rewrite fmap_length.
        rewrite take_length_le.
        1: done.
        { rewrite fmap_length in HlastModifiedLen. word. }
      }
      Unshelve.
      { destruct H1 as [? ?].
        exists (get_rwops x). rewrite -fmap_app. unfold get_rwops.
        by rewrite H1.
      }
      {
        exists (get_rwops (drop (int.nat lastModifiedIndex) st.(server.ops_full_eph))).
        rewrite -fmap_app. rewrite take_drop. done.
      }
    }
    wp_loadField.
    iClear "HopAppliedConds_conds HcommittedNextIndex_is_cond".
    iNamed "Hvol".
    wp_apply (wp_condWait with "[-Err Reply Hrep_sl HlastModified]").
    {
      iFrame "#".
      iFrame "Hlocked".
      repeat iExists _; iSplitR "HghostEph"; last by iFrame.
      repeat iExists _; iFrame "∗#%".
    }
    iIntros "[Hlocked Hown]".
    wp_pures.
    iModIntro. iLeft.
    iSplitR; first done.
    iFrame.
  }
  { (* case: lease is expired *)
    iModIntro.
    iFrame.
    wp_pures.
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    2:{ exfalso. word. }
    wp_loadField.
    wp_apply (release_spec with "[-Err Reply HlastModified Hrep_sl]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat iExists _; iSplitR "HghostEph"; last by iFrame.
      repeat iExists _; iFrame "∗#%".
    }
    wp_pures.
    wp_storeField.
    iModIntro.
    iIntros "HΦ".
    iApply ("HΦ" $! (ApplyReply.mkC _ _)).
    2:{
      iExists _, _. iFrame.
    }
    { by iApply "Hfail_Φ". }
  }
Qed.

End pb_roapply_proof.
