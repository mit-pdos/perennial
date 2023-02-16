From Perennial.base_logic Require Import lib.saved_prop.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_ghost.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_marshal_proof pb_applybackup_proof pb_apply_proof.
(* FIXME: importing apply_proof for some lemmas *)
From Perennial.program_proof.reconnectclient Require Import proof.

Section pb_roapply_proof.

Context `{!heapGS Σ}.
Context {pb_record:PBRecord}.

Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation compute_reply := (pb_compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).

Context `{!pbG Σ}.

Lemma wp_Clerk__ApplyRo γ γsys γsrv ck op_sl q op (op_bytes:list u8) (Φ:val → iProp Σ) :
has_op_encoding op_bytes op →
is_Clerk ck γsys γsrv -∗
is_inv γ γsys -∗
is_slice_small op_sl byteT q op_bytes -∗
□((|={⊤∖↑pbN,∅}=> ∃ ops, own_log γ ops ∗
  (own_log γ ops ={∅,⊤∖↑pbN}=∗
     (∀ reply_sl, is_slice_small reply_sl byteT 1 (compute_reply ops op) -∗
            is_slice_small op_sl byteT q op_bytes -∗
                Φ (#(U64 0), slice_val reply_sl)%V)))
∗
(∀ (err:u64) unused_sl, ⌜err ≠ 0⌝ -∗ is_slice_small op_sl byteT q op_bytes -∗
                                     Φ (#err, (slice_val unused_sl))%V )) -∗
WP Clerk__ApplyRo #ck (slice_val op_sl) {{ Φ }}.
Proof.
  intros Henc.
  iIntros "#Hck #Hinv Hop_sl".
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
    iDestruct "Hsrv" as "(_ & _ & _ & _ & _ & _ & $ & _)".
  }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold Apply_spec.
    iExists _, _.
    iSplitR; first done.
    iSplitR; first done.
    simpl.
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
      iMod ("HΦ" with "Hlog") as "HΦ".
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

Lemma get_rwops_single_nil :
  ∀ A op Q, get_rwops (A:=A) (pb_record:=pb_record) [(ro_op op, Q)] = [].
Proof.
  unfold get_rwops.
  done.
Qed.

Local Hint Rewrite get_rwops_single_nil.

Lemma wp_Server__ApplyRo_internal (s:loc) γ γsrv op_sl op_bytes op Q :
  {{{
        is_Server s γ γsrv ∗
        readonly (is_slice_small op_sl byteT 1 op_bytes) ∗
        ⌜has_op_encoding op_bytes op⌝ ∗
        (|={⊤∖↑ghostN,∅}=> ∃ σ, own_ghost γ σ ∗ (own_ghost γ (σ ++ [(ro_op op, Q)]) ={∅,⊤∖↑ghostN}=∗ True))
  }}}
    pb.Server__ApplyRo #s (slice_val op_sl)
  {{{
        reply_ptr reply, RET #reply_ptr; £ 1 ∗ £ 1 ∗ £ 1 ∗ ApplyReply.own_q reply_ptr reply ∗
        if (decide (reply.(ApplyReply.err) = 0%Z)) then
          ∃ opsfull,
            let ops := (get_rwops opsfull) in
            ⌜reply.(ApplyReply.ret) = compute_reply ops op⌝ ∗
            is_ghost_lb γ (opsfull ++ [(ro_op op, Q)])
        else
          True
  }}}
  .
Proof.
  iIntros (Φ) "[#His Hpre] HΦ".
  iDestruct "Hpre" as "(#Hsl & %Hghostop_op & Hupd)".
  iNamed "His".
  rewrite /Server__ApplyRo.
  wp_pure1_credit "Hlc1".
  wp_pure1_credit "Hlc2".
  wp_pure1_credit "Hlc3".
  iCombine "Hlc1 Hlc2 Hlc3" as "Hlcs".
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

  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_if_destruct.
  { (* return error "not primary" *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ Err Reply Hlcs]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat (iExists _).
      iFrame "Hstate ∗#"; iFrame "%".
    }
    wp_pures.
    wp_storeField.
    iApply "HΦ".
    iDestruct "Hlcs" as "($ & $ & $)".
    iSplitL "Err Reply".
    {
      instantiate (1:=(ApplyReply.mkC _ _)).
      iExists _.
      iFrame.
      iExists 1%Qp.
      iApply is_slice_small_nil.
      done.
    }
    done.
  }
  wp_loadField.

  wp_if_destruct.
  { (* return ESealed *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ Err Reply Hlcs]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat (iExists _).
      iFrame "∗#"; iFrame "%".
    }
    wp_pures.
    wp_storeField.
    iApply ("HΦ" $! _ (ApplyReply.mkC 1 [])).
    iDestruct "Hlcs" as "($ & $ & $)".
    iFrame.
    iExists _, 1%Qp; iFrame.
    iApply is_slice_small_nil.
    done.
  }

  clear Heqb.

  (* make proposal *)
  iAssert (_) with "HprimaryOnly" as "HprimaryOnly2".
  iEval (rewrite /is_possible_Primary /tc_opaque) in "HprimaryOnly2".
  iNamed "HprimaryOnly2".
  iAssert (_) with "HisSm" as "HisSm2".
  iEval (rewrite /is_StateMachine /tc_opaque) in "HisSm2".
  iNamed "HisSm2".
  wp_loadField.
  wp_loadField.

  (* make ephemeral proposal first *)
  iMod (own_update with "Heph") as "Heph".
  {
    apply singleton_update.
    apply mono_list_update.
    instantiate (1:=opsfull_ephemeral ++ [(ro_op op, Q)]).
    by apply prefix_app_r.
  }
  iDestruct (own_mono _ _ {[ _ := ◯ML _ ]} with "Heph") as "#Hnew_eph_lb".
  {
    apply singleton_mono.
    apply mono_list_included.
  }

  iApply fupd_wp.
  iMod (fupd_mask_subseteq (↑pbN)) as "Hmask".
  { set_solver. }
  iMod (valid_add with "Hlc4 Heph_valid [Hupd]") as "#Hnew_eph_valid".
  {
    iMod "Hupd" as (?) "[Hghost Hupd]".
    iModIntro.
    iExists _; iFrame.
    iIntros. done.
  }
  iMod "Hmask".
  iModIntro.

  (* NOTE: unlike Apply(), don't (and actually *can't* ) need to add to own_proposal. It is enough to
     add to ephemeral_proposal. The applyRoThread() will handle appending to
     own_proposal.
   *)
  wp_apply ("HapplyReadonlySpec" with "[HisSm $Hstate $Hsl]").
  { done. }
  iIntros (reply_sl q) "(Hreply & Hstate)".

  wp_storeField.
  wp_loadField.
  wp_apply (std_proof.wp_SumAssumeNoOverflow).
  iIntros "%Hno_overflow".
  wp_storeField.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_pures.
  (* Possibly wake up the applyRoThread background goroutine, only if the
     current nextIndex is durable *)
  wp_apply (wp_If_optional with "[] [HroOpsToPropose_cond]").
  2:{
    iNamedAccu.
  }
  {
    iIntros (?).
    iNamed 1. iIntros "HΦ".
    wp_loadField.
    wp_apply (wp_condSignal with "[]").
    { iFrame "#". }
    by iApply "HΦ".
  }
  iNamed 1.

  wp_pures.

  (* Wait for the background thread to do the committing *)
  iAssert (pb_definitions.own_Server s γ γsrv γeph _ mu) with "[-HΦ Hlcs Reply Err Hreply Hlocked]" as "Hown".
  {
    repeat iExists _.
    iFrame "Hsealed Heph".
    replace (get_rwops (opsfull_ephemeral ++ [(ro_op op, Q)])) with (get_rwops (opsfull_ephemeral)); last first.
    {
      rewrite get_rwops_app.
      unfold get_rwops.
      simpl.
      rewrite app_nil_r.
      done.
    }
    iFrame "∗".
    iFrame "#".
    iFrame "%".

    (* establish new is_possible_Primary, because we increased nextRoIndex *)
    repeat iExists _.
    iFrame "Hcommit_lb #".
    iFrame "%".
    iPureIntro.
    destruct Heph_proposal as (opsfull_eph_ro & Hsuffix & HnextRoIndex & HroOnly & Hfull).
    exists (opsfull_eph_ro ++ [(ro_op op, Q)]).
    split.
    {
      apply suffix_app.
      { done. }
    }
    split.
    {
      rewrite app_length.
      simpl.
      word.
    }
    split.
    {
      rewrite get_rwops_app.
      rewrite HroOnly.
      simpl.
      unfold get_rwops.
      done.
    }
    { by apply contains_app. }
  }

  wp_forBreak.

  wp_pures.
  iClear "Hs_epoch_lb HopAppliedConds_conds HdurableNextIndex_is_cond HroOpsToPropose_is_cond".
  iClear "HcommittedNextRoIndex_is_cond Hdurable_lb Heph_prop_lb Hcommit_lb HprimaryOnly HisSm Heph_commit_lb Heph_valid".
  clear dependent committedNextIndex committedNextRoIndex.
  iNamed "Hown".
  wp_loadField.
  wp_pures.

  (* compound condition in if statement *)
  wp_bind (if: (if: #_ then _ else _) then _ else _)%E.
  wp_apply (wp_wand with "[HcommittedNextIndex HcommittedNextRoIndex]").
  {
    instantiate (1:=(λ v,
                  ⌜v = #(bool_decide (epoch ≠ epoch0 ∨
                                    (int.nat nextIndex < int.nat committedNextIndex) ∨
                                    (int.nat committedNextRoIndex >= int.nat nextRoIndex + 1)
                                   ))⌝ ∗ _
                )%I).
    wp_bind (if: #_ then _ else _)%E.
    wp_if_destruct.
    {
      wp_pures.
      iSplitR; last first.
      {
        iModIntro. iNamedAccu.
      }
      iPureIntro.
      f_equal.
      rewrite bool_decide_true; first done.
      left.
      naive_solver.
    }
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    {
      iFrame.
      iPureIntro.
      f_equal.
      rewrite bool_decide_true; first done.
      right.
      left.
      word.
    }
    {
      wp_loadField.
      wp_pures.
      iFrame.
      iPureIntro.
      repeat f_equal.
      apply bool_decide_ext.
      split.
      {
        intros Hineq.
        right; right.
        word.
      }
      {
        intros [Hcase|[Hcase|Hcase]].
        { exfalso. done. }
        { exfalso. word. }
        word.
      }
    }
  }
  iIntros (?) "(%Hre & HH)".
  iNamed "HH".
  subst v.
  wp_if_destruct; last first.
  { (* keep waiting *)
    wp_loadField.
    wp_apply (wp_condWait with "[-HΦ Hlcs Reply Err Hreply]").
    {
      iFrame "HmuInv HcommittedNextRoIndex_is_cond".
      iFrame "Hlocked".
      repeat iExists _.
      iFrame "∗#".
      iFrame "%".
    }
    iIntros "[Hlocked Hown]".
    wp_pures.
    iLeft.
    iModIntro.
    iFrame "∗".
    done.
  }
  (* break, either done with RO op, or have non-retryable error *)
  iRight.
  iModIntro.
  iSplitR; first done.
  wp_pures.
  wp_loadField.

  wp_if_destruct.
  { (* epoch has changed, return error *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ Hlcs Reply Err Hreply]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat iExists _.
      iFrame "∗#"; iFrame "%".
    }
    wp_pures.
    wp_storeField.
    iApply "HΦ".
    iDestruct "Hlcs" as "($ & $ & $)".
    iSplitL.
    {
      instantiate (1:=ApplyReply.mkC _ _).
      iExists _, q%Qp; iFrame.
      simpl.
      iModIntro.
      done.
    }
    simpl.
    erewrite decide_False.
    { iModIntro. done. }
    { naive_solver. }
  }

  wp_loadField.

  (* XXX: need to establish is_ghost_lb with the (ro_op op,Q) at the end of it *)
  (* FIXME: either check in code or prove in proof that (isPrimary = true) *)
  destruct isPrimary; last admit.

  (* there are two cases, either a new RW op was committed, or the RO commit
     index is big enough *)
  iAssert ((is_ghost_lb γ (opsfull_ephemeral ++ [(ro_op op, Q)])))%I with "[-]" as "#Hnew_commit_lb".
  {
    destruct Heqb as [Hbad|Hcases].
    { by exfalso. }

    iAssert (_) with "HprimaryOnly" as "HprimaryOnly2".
    iEval (rewrite /is_possible_Primary /tc_opaque) in "HprimaryOnly2".
    iClear "Htok_used_witness Hconf Hclerkss_sl Hclerkss_rpc".
    iNamed "HprimaryOnly2".

    iDestruct (own_valid_2 with "Heph_commit_lb Hnew_eph_lb") as %Hvalid.
    rewrite singleton_op singleton_valid in Hvalid.
    apply mono_list_lb_op_valid_1_L in Hvalid.

    (* FIXME: in the second case, want to assume HnewRw is false *)

    iApply (own_mono with "Hcommit_lb").
    apply mono_list_lb_mono.
    destruct (decide (int.nat nextIndex < int.nat committedNextIndex)) as [HnewRw|HnoNewRw].
    (* destruct Hcases as [HnewRw|HroCommitted]. *)
    (* can't just destruct Hcases because want to know that the first is
       definitely false when in the second case *)
    { (* in this case, there are new RW ops past the one the RO was applied on
         top of. *)
      destruct Hvalid as [Hbad|Hprefix].
      { (* this case should be impossible because the committed list should
           contain an RW op after the eph_proposal_lb *)
        exfalso.
        apply get_rwops_prefix, prefix_length in Hbad.
        rewrite get_rwops_app /= in Hbad.
        rewrite get_rwops_single_nil app_nil_r in Hbad.
        rewrite HcommitLen0 Hσ_nextIndex in Hbad.
        word.
      }
      (* extract the lower bound *)
      done.
    }
    { (* in this case, the RO op has been explicitly committed *)
      destruct Hcases as [|].
      { exfalso. word. }
      destruct Hvalid as [Hprefix|Hprefix].
      { (* in this case, the commit_full list is prefix of the opsfull_eph +
           ro_op op, and needs to be updated. *)

        (* Argument:
           len(get_rws ops_commit_full0) = len(get_rws opsfull_ephemeral)
           ops_commit_full0 has committedNextRoIndex many RO ops as suffix
           ops_ephemeral has nextRoIndex many RO ops as suffix
         *)

        destruct HcommitRoLen as (ops_commit_ro & HcommitRoSuffix & HcommitRoLen & HisRoCommit & HfullSuffixCommit).
        destruct Heph_proposal as (ops_eph_ro & HephRoSuffix & HephRoLen & HisRoEph & HfullSuffix).

        apply prefix_app_cases in Hprefix.
        destruct Hprefix as [HprefixBad|Hgood].
        {
          exfalso.
          epose proof (roapply_helper _ _ _ _ HfullSuffix HfullSuffixCommit HprefixBad _ HcommitRoSuffix HisRoCommit) as HroPrefix.
          apply prefix_length in HroPrefix.
          Unshelve.
          2:{
            apply list_prefix_eq.
            { by apply get_rwops_prefix. }
            { rewrite Hσ_nextIndex. rewrite HcommitLen0.
              admit. (* FIXME: use opsfull_ephemeral ⪯ opsfull_ephemeral0 *)
            }
          }

          word.
        }
        rewrite Hgood.
        done.
      }
      {
        (* in this case, the committed list already contains what we're looking for (ro_op op). *)
        done.
      }
    }
  }

  wp_apply (release_spec with "[-HΦ Hlcs Reply Err Hreply]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    repeat (iExists _).
    iFrame "∗#"; iFrame "%".
  }
  wp_pures.
  wp_storeField.
  iApply "HΦ".
  iDestruct "Hlcs" as "($ & $ & $)".
  iSplitL.
  {
    instantiate (1:=ApplyReply.mkC _ _).
    iExists _, _; iFrame.
    iModIntro. done.
  }
  simpl.
  erewrite decide_True.
  {
    iModIntro. iExists _.
    iFrame "Hnew_commit_lb".
    done.
  }
  { done. }
Admitted.

Lemma wp_Server__ApplyRo (s:loc) γlog γ γsrv op_sl op (enc_op:list u8) Ψ (Φ: val → iProp Σ) :
  is_Server s γ γsrv -∗
  readonly (is_slice_small op_sl byteT 1 enc_op) -∗
  (∀ reply, Ψ reply -∗ ∀ reply_ptr, ApplyReply.own_q reply_ptr reply -∗ Φ #reply_ptr) -∗
  ApplyRo_core_spec γ γlog op enc_op Ψ -∗
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
