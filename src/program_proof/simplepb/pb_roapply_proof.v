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
Context {pb_record:Sm.t}.

Notation OpType := (Sm.OpType pb_record).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).

Print pb_definitions.pbG.
Context `{!pbG Σ}.

Lemma wp_Clerk__ApplyRo γ γsrv ck op_sl q op (op_bytes:list u8) (Φ:val → iProp Σ) :
has_op_encoding op_bytes op →
is_Clerk ck γ γsrv -∗
is_slice_small op_sl byteT q op_bytes -∗
□((|={⊤∖↑pbN,∅}=> ∃ ops, own_op_log γ ops ∗
  (own_op_log γ ops ={∅,⊤∖↑pbN}=∗
     □(∀ reply_sl, is_slice_small reply_sl byteT 1 (compute_reply ops op) -∗
            is_slice_small op_sl byteT q op_bytes -∗
                Φ (#(U64 0), slice_val reply_sl)%V)))
∗
(∀ (err:u64) unused_sl, ⌜err ≠ 0⌝ -∗ is_slice_small op_sl byteT q op_bytes -∗
                                     Φ (#err, (slice_val unused_sl))%V )) -∗
WP Clerk__ApplyRo #ck (slice_val op_sl) {{ Φ }}.
Proof.
  intros Henc.
  iIntros "#Hck Hop_sl".
  iIntros "#HΦ".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep) "Hrep".
  wp_pures.
  iNamed "Hck".
  wp_loadField.
  rewrite is_pb_host_unfold.
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
    "#HapplySpec" ∷ is_ApplyReadonlyFn (pb_record:=pb_record) own_StateMachine applyFn P
  )
.
Proof.
  rewrite /is_StateMachine /tc_opaque.
  iNamed 1. iExists _; iFrame "#".
Qed.

Lemma preread_step st γ γsrv t Q {own_StateMachine} :
  st.(server.leaseValid) = true →
  int.nat t < int.nat st.(server.leaseExpiration) →
  £ 1 -∗
  £ 1 -∗
  £ 1 -∗
  own_time t -∗
  □(|={⊤ ∖ ↑pbN,∅}=>
    ∃ σ, own_pre_log γ.(s_prelog) σ ∗
      (own_pre_log γ.(s_prelog) σ ={∅,⊤ ∖ ↑pbN}=∗ □ Q σ)) -∗
  own_Server_ghost_eph_f st γ γsrv -∗
  accessP_fact own_StateMachine (own_Server_ghost_f γ γsrv) -∗
  own_StateMachine st.(server.epoch) (get_rwops st.(server.ops_full_eph)) st.(server.sealed) (own_Server_ghost_f γ γsrv) -∗
  sys_inv γ.(s_pb) -∗
  |NC={⊤}=>
  own_StateMachine st.(server.epoch) (get_rwops st.(server.ops_full_eph)) st.(server.sealed) (own_Server_ghost_f γ γsrv) ∗
  preread_inv γ.(s_pb) γ.(s_prelog) γ.(s_reads) ∗
  is_proposed_read γ.(s_reads) (length st.(server.ops_full_eph)) Q ∗
  own_time t ∗
  own_Server_ghost_eph_f st γ γsrv.
Proof.
  iIntros (??) "Hlc Hlc2 Hlc3 Htime #Hupd Hghost #HaccP Hstate #HpbInv".
  iEval (rewrite /own_Server_ghost_eph_f /tc_opaque) in "Hghost".
  iNamed "Hghost".
  iNamed "Hlease".
  rewrite H.
  iDestruct "Hlease" as (??) "(#HconfInv & #Hlease & #Hlease_lb)".

  (* Step 1. use accessP_fact to get ownership of locally accepted state *)
  iMod ("HaccP" with "Hlc [-Hstate] Hstate") as "$"; last done.
  iIntros (???) "Hghost".
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
    iDestruct (big_sepS_elem_of_acc _ _ epoch with "Hunused") as "[HH _]".
    { set_solver. }
    iSpecialize ("HH" with "[%]").
    { word. }
    iDestruct "HH" as "(_ & Hunset & _)".
    unfold is_epoch_config.
    iDestruct "HsomeConf" as "[HsomeConf _]".
    iDestruct (own_valid_2 with "Hunset HsomeConf") as %Hbad.
    exfalso.
    rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in Hbad.
    by destruct Hbad as [Hbad _].
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

  iMod (start_read_step with "Hlc2 [$] [Hupd] Hcommit") as "[$ Hcommit]".
  { solve_ndisj. }
  { by apply prefix_length. }
  {
    iModIntro.
    iMod (fupd_mask_subseteq (⊤∖↑pbN)) as "Hmask".
    { solve [eauto 20 with ndisj]. } (* FIXME: increase search depth? *)
    iMod "Hupd" as (?) "[? Hupd]".
    iModIntro. iExists _; iFrame.
    iIntros "?". iMod ("Hupd" with "[$]").
    by iMod "Hmask".
  }
  iMod ("HclosePb" with "[-Htime Hprimary Hghost]").
  { iNext; repeat iExists _; iFrame "∗#". }
  iModIntro.
  iFrame.
  iSplitL "Hghost".
  { repeat iExists _; iFrame "∗#%". }
  iFrame "#".
  iEval (rewrite /own_Server_ghost_eph_f /tc_opaque).
  iFrame "∗#%".
  repeat iExists _; iFrame "∗#%".
  rewrite H.
  repeat iExists _; iFrame "∗#%".
Qed.

Lemma wp_Server__ApplyRo (s:loc) γ.(s_log) γ γsrv op_sl op (enc_op:list u8) Ψ (Φ: val → iProp Σ) :
  is_Server s γ γsrv -∗
  readonly (is_slice_small op_sl byteT 1 enc_op) -∗
  (∀ reply, Ψ reply -∗ ∀ reply_ptr, ApplyReply.own_q reply_ptr reply -∗ Φ #reply_ptr) -∗
  ApplyRo_core_spec γ γ.(s_log) op enc_op Ψ -∗
  WP (pb.Server__ApplyRoWaitForCommit #s (slice_val op_sl)) {{ Φ }}
.
Proof.
  iIntros "#Hsrv #Hop_sl".
  iIntros "HΨ HΦ".
  iApply (wp_frame_wand with "HΨ").
  iDestruct "HΦ" as "(%Hop_enc & #Hinv & #Hupd & #Hfail_Φ)".
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
  { (* not primary *)
    (* FIXME: remove this unnecessary check *)
    admit.
  }
  wp_loadField.
  wp_pures.
  wp_if_destruct.
  { (* sealed *)
    (* FIXME: remove this unnecessary check *)
    admit.
  }
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
      rewrite Heqb0 Heqb.
      iFrame "∗#%".
    }
    wp_pures.
    wp_storeField.
    iModIntro.
    iIntros "HΨ".
    iApply ("HΨ" $! (ApplyReply.mkC _ _)).
    2:{
      iExists _, _; iFrame.
      by iApply is_slice_small_nil.
    }
    { by iApply "Hfail_Φ". }
  }

  wp_apply wp_GetTimeRange.
  iIntros (?????) "Htime".
  destruct (decide (int.nat h < int.nat st.(server.leaseExpiration))).
  { (* case: got lease is not expired *)

    (* proof steps here:
       use accessP to get accepted ↦ σ, with (σ ⪯ ops).
       a
       Combine with
     *)
    iDestruct (preread_step with "Hlc1 Hlc2 Hlc3 Htime [] HghostEph [] [Hstate] [$]") as (?) ">HH".
    { done. }
    { word. }
    {
      iModIntro.
      iExactEq "Hupd".
      (* FIXME: need to straighten out γ.(s_log)s. *)
    }

    iModIntro. iFrame "Htime".
    wp_pures.
    wp_loadField.
    wp_if_destruct.
    { exfalso. word. }
    wp_loadField.
    iDestruct (is_StateMachine_acc_applyReadonly with "HisSm") as "H".
    iNamed "H".
    wp_loadField.
    wp_apply ("HapplySpec" with "[$Hstate]").
    {
      iSplitL; first done.
      iFrame "#".
    }
    iIntros (??) "[Hrep_sl Hstate]".
    wp_storeField.
    wp_loadField.
    wp_loadField.
    wp_pures.

    iAssert (mu_inv s γ γsrv mu) with "[-Err Reply Hlcs HΦ]" as "Hown".
    wp_forBreak_cond.
  }
  (* *)

Qed.

Lemma wp_Server__ApplyRo (s:loc) γ.(s_log) γ γsrv op_sl op (enc_op:list u8) Ψ (Φ: val → iProp Σ) :
  is_Server s γ γsrv -∗
  readonly (is_slice_small op_sl byteT 1 enc_op) -∗
  (∀ reply, Ψ reply -∗ ∀ reply_ptr, ApplyReply.own_q reply_ptr reply -∗ Φ #reply_ptr) -∗
  ApplyRo_core_spec γ γ.(s_log) op enc_op Ψ -∗
  WP (pb.Server__ApplyRo #s (slice_val op_sl)) {{ Φ }}
.
Proof using Type*.
  iIntros "#Hsrv #Hop_sl".
  iIntros "HΨ HΦ".
  iApply (wp_frame_wand with "HΨ").
  iDestruct "HΦ" as "(%Hop_enc & #Hinv & #Hupd & Hfail_Φ)".
  iMod (ghost_var_alloc (())) as (γtok) "Htok".
  set (OpPred :=
       (λ ops, inv escrowN (
        Ψ (ApplyReply.mkC 0 (compute_reply ops op)) ∨
          ghost_var γtok 1 ()
        ))).

  iMod (saved_pred_alloc OpPred DfracDiscarded) as (γghost_op) "#Hsaved"; first done.
  iApply wp_fupd.
  wp_apply (wp_Server__ApplyRo_internal _ _ _ _ _
      op γghost_op
             with "[$Hsrv $Hop_sl Hupd]").
  {
    iSplitL ""; first done.
    iInv "Hinv" as "HH" "Hclose".
    iDestruct "HH" as (?) "(Hghost & >Hlog & #HQs)".
    iDestruct "Hghost" as (σgnames) "(>Hghost&>%Hfst_eq&#Hsaved')".
    iMod (fupd_mask_subseteq (⊤∖↑pbN)) as "Hmask".
    {
      assert ((↑ghostN:coPset) ⊆ (↑pbN:coPset)).
      { apply nclose_subseteq. }
      assert ((↑appN:coPset) ⊆ (↑pbN:coPset)).
      { apply nclose_subseteq. }
      set_solver.
    }
    iMod "Hupd".
    iModIntro.
    iDestruct "Hupd" as (σ0) "[Hlog2 Hupd]".
    iDestruct (own_valid_2 with "Hlog Hlog2") as %Hvalid.
    apply mono_list_auth_dfrac_op_valid_L in Hvalid.
    destruct Hvalid as [_ <-].
    iExists _; iFrame.
    iIntros "Hghost".
    iMod ("Hupd" with "Hlog2") as "Hupd".

    iAssert (|={↑escrowN}=> inv escrowN ((Ψ (ApplyReply.mkC 0 (compute_reply (get_rwops opsfullQ) op)))
                                  ∨ ghost_var γtok 1 ()))%I
            with "[Hupd]" as "Hinv2".
    {
      iMod (inv_alloc with "[-]") as "$"; last done.
      iNext.
      iIntros.
      iLeft.
      iIntros.
      iApply "Hupd".
    }
    iMod "Hmask" as "_".
    iMod (fupd_mask_subseteq (↑escrowN)) as "Hmask".
    {
      assert ((↑escrowN:coPset) ## (↑ghostN:coPset)).
      { by apply ndot_ne_disjoint. }
      assert ((↑escrowN:coPset) ## (↑appN:coPset)).
      { by apply ndot_ne_disjoint. }
      set_solver.
    }
    iMod "Hinv2" as "#HΦ_inv".
    iMod "Hmask".

    iMod ("Hclose" with "[HQs Hghost Hlog]").
    {
      iNext.
      iExists (opsfullQ ++ [(ro_op op, OpPred)]); iFrame.
      iSplitL "Hghost".
      { iExists _. iFrame.
        iSplitL.
        { iPureIntro. rewrite ?fmap_app /=. congruence. }
        rewrite ?fmap_app. iApply big_sepL2_app.
        { iFrame "Hsaved'". }
        iApply big_sepL2_singleton. iFrame "Hsaved".
      }
      rewrite get_rwops_app.
      rewrite get_rwops_single_nil.
      rewrite app_nil_r.
      iFrame.

      iModIntro.
      iIntros.
      apply prefix_app_cases in H as [Hprefix_of_old|Hnew].
      {
        iApply "HQs".
        { done. }
        { done. }
      }
      {
        rewrite Hnew in H0.
        assert (opsfullQ = opsPrePre) as ->.
        { (* TODO: list_solver. *)
          apply (f_equal reverse) in H0.
          rewrite reverse_snoc in H0.
          rewrite reverse_snoc in H0.
          inversion H0.
          apply (f_equal reverse) in H2.
          rewrite reverse_involutive in H2.
          rewrite reverse_involutive in H2.
          done.
        }
        eassert (_ = lastEnt) as <-.
        { eapply (suffix_snoc_inv_1 _ _ _ opsPrePre). rewrite -H0.
          done. }
        simpl.
        unfold OpPred.
        iFrame "#".
      }
    }
    done.
  }
  iIntros (err reply).
  iIntros "(Hcred & Hcred2 & Hcred3 & Hreply & Hpost)".
  destruct (decide (reply.(ApplyReply.err) = U64 0)).
  { (* no error *)
    iNamed "Hreply".
    rewrite e.
    iDestruct "Hpost" as (?) "[%Hrep #Hghost_lb]".
    rewrite Hrep.
    iInv "Hinv" as "HH" "Hclose".
    {
      iDestruct "HH" as (?) "(Hghost & >Hlog & #HQs)".
      iDestruct "Hghost" as (σgnames) "(>Hghost&>%Hfst_eq&#Hsaved')".
      iApply (lc_fupd_add_later with "Hcred").
      iNext.
      iDestruct (own_valid_2 with "Hghost Hghost_lb") as %Hvalid.
      rewrite mono_list_both_dfrac_valid_L in Hvalid.
      destruct Hvalid as [_ Hvalid].

      destruct Hvalid as (σtail&Hvalid').
      subst.
      iDestruct (big_sepL2_length with "Hsaved'") as %Hlen.
      rewrite ?fmap_length in Hlen.
      assert (∃ σ0a op' Q' σ0b,
                 opsfullQ = σ0a ++ [(op', Q')] ++ σ0b ∧
                 length σ0a = length opsfull ∧
                 length σ0b = length σtail) as (σ0a&op'&Q'&σ0b&Heq0&Hlena&Hlenb).
      {

        destruct (nth_error opsfullQ (length opsfull)) as [(op', Q')|] eqn:Hnth; last first.
        { apply nth_error_None in Hnth. rewrite ?app_length /= in Hlen. lia. }
        edestruct (nth_error_split opsfullQ (length opsfull)) as (l1&l2&Heq&Hlen'); eauto.
        eexists l1, _, _, l2. rewrite Heq /=; split_and!; eauto.
        rewrite Heq ?app_length /= in Hlen. rewrite Hlen' in Hlen. clear -Hlen.
        (* weird, lia fails directly but if you replace lengths with a nat then it works... *)
        remember (length l2) as k.
        remember (length σtail) as k'. rewrite Heqk in Hlen. rewrite -Heqk' in Hlen. lia.
      }

      iDestruct ("HQs" $! (σ0a ++ [(op', Q')]) _ (_, _) with "[] []") as "#HQ".
      { rewrite Heq0. iPureIntro; eexists; eauto. rewrite app_assoc.  done. }
      { done. }
      simpl.
      iMod ("Hclose" with "[Hghost Hlog]") as "_".
      {
        iNext.
        iExists _; iFrame "∗#".
        iExists _. iFrame.
        iSplit.
        { iPureIntro. auto. }
        iApply "Hsaved'".
      }

      rewrite Heq0. rewrite ?fmap_app -app_assoc. iDestruct (big_sepL2_app_inv with "Hsaved'") as "(H1&H2)".
      { left. rewrite ?fmap_length //. }

      iEval (simpl) in "H2". iDestruct "H2" as "(HsavedQ'&?)".
      iDestruct (saved_pred_agree _ _ _ _  _ (get_rwops σ0a) with "Hsaved [$]") as "HQequiv".
      iApply (lc_fupd_add_later with "[$]"). iNext.
      iRewrite -"HQequiv" in "HQ".

      iInv "HQ" as "Hescrow" "Hclose".
      iDestruct "Hescrow" as "[HΦ|>Hbad]"; last first.
      {
        iDestruct (ghost_var_valid_2 with "Htok Hbad") as %Hbad.
        exfalso. naive_solver.
      }
      iMod ("Hclose" with "[$Htok]").
      iMod (lc_fupd_elim_later with "Hcred2 HΦ") as "HΦ".
      iModIntro.
      iIntros "HΨ".
      iApply ("HΨ" with "HΦ").
      iExists _, _.
      iFrame.
      simpl.
      rewrite /named.
      iExactEq "Hrepy_ret_sl".
      { repeat f_equal.
        rewrite Heq0 in Hfst_eq. rewrite ?fmap_app -app_assoc in Hfst_eq.
        apply app_inj_1 in Hfst_eq; last (rewrite ?fmap_length //).
        destruct Hfst_eq as (Hfst_eq&_).
        apply (get_rwops_fst σ0a opsfull) in Hfst_eq as ->.
        done.
      }
    }
  }
  {
    iIntros.
    iNamed "Hreply".
    iModIntro.
    iIntros "HΨ".
    iApply ("HΨ" with "[Hfail_Φ]").
    {
      iApply "Hfail_Φ".
      done.
    }
    iExists _, _.
    iFrame.
  }
Qed.

End pb_roapply_proof.
