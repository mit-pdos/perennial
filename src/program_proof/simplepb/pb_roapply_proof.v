From Perennial.base_logic Require Import lib.saved_prop.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_protocol.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_marshal_proof pb_applybackup_proof pb_apply_proof.
(* FIXME: importing apply_proof for some lemmas *)
From Perennial.program_proof.reconnectclient Require Import proof.

Section pb_roapply_proof.

Context `{!heapGS Σ}.
Context {pb_record:Sm.t}.

Notation OpType := (Sm.OpType pb_record).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).

Context `{!pbG Σ}.

Lemma wp_Clerk__ApplyRo γlog γsys γsrv ck op_sl q op (op_bytes:list u8) (Φ:val → iProp Σ) :
has_op_encoding op_bytes op →
is_Clerk ck γsys γsrv -∗
is_inv γlog γsys.1 -∗
is_slice_small op_sl byteT q op_bytes -∗
□((|={⊤∖↑pbN,∅}=> ∃ ops, own_log γlog ops ∗
  (own_log γlog ops ={∅,⊤∖↑pbN}=∗
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
    iDestruct "Hsrv" as "(_ & _ & _ & _ & _ & $ & _)".
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

Lemma wp_Server__ApplyRo_internal (s:loc) γlog γ γsrv op_sl op_bytes op Q :
  {{{
        is_Server s γ γsrv ∗
        readonly (is_slice_small op_sl byteT 1 op_bytes) ∗
        ⌜has_op_encoding op_bytes op⌝ ∗
        (|={⊤∖↑ghostN,∅}=> ∃ σ, own_ghost γlog σ ∗ (own_ghost γlog (σ ++ [(op, Q)]) ={∅,⊤∖↑ghostN}=∗ True))
  }}}
    pb.Server__ApplyRoWaitForCommit #s (slice_val op_sl)
  {{{
        reply_ptr reply, RET #reply_ptr; £ 1 ∗ £ 1 ∗ £ 1 ∗ ApplyReply.own_q reply_ptr reply ∗
        if (decide (reply.(ApplyReply.err) = 0%Z)) then
          ∃ opsfull,
            let ops := (get_rwops opsfull) in
            ⌜reply.(ApplyReply.ret) = compute_reply ops op⌝ ∗
            is_ghost_lb γlog (opsfull ++ [(op, Q)])
        else
          True
  }}}
  .
Proof.
  iIntros (Φ) "[#His Hpre] HΦ".
  iDestruct "Hpre" as "(#Hsl & %Hghostop_op & Hupd)".
  iNamed "His".
  rewrite /Server__ApplyRoWaitForCommit.
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
    wp_apply (release_spec with "[-Hlcs HΦ Hupd Err Reply]").
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
    iApply ("HΦ" $! _ (ApplyReply.mkC _ _)).
    iDestruct "Hlcs" as "($ & $ & $)".
    iModIntro.
    iSplitL.
    { iExists _, _; iFrame.
      by iApply is_slice_small_nil.
    }
    simpl.
    destruct decide.
    { by exfalso. }
    done.
  }

  wp_apply wp_GetTimeRange.
  iIntros (?????) "Htime".
  destruct (decide (int.nat h <= int.nat st.(server.leaseExpiration))).
  { (* case: got lease is not expired *)
    iModIntro. iFrame "Htime".
    wp_pures.
    wp_loadField.
    wp_if_destruct.
    { exfalso. word. }
    wp_loadField.
    wp_storeField.
  }
  (* *)

Qed.

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
