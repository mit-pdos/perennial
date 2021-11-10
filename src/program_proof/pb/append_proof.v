From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import pb.

From Perennial.program_proof.pb Require Export common_proof append_marshal_proof replica_defns replica_ghost_proof.

Section append_proof.

Context `{!heapGS Σ}.

Lemma wp_ReplicaServer__AppendRPC (s:loc) rid γ (args_ptr:loc) args :
  {{{
       "#HisRepl" ∷ is_ReplicaServer s rid γ ∗
       "Hargs" ∷ own_AppendArgs args_ptr args ∗
       "#Hproposal_lb_in" ∷ proposal_lb γ args.(AA_cn) args.(AA_log) ∗
       "#HoldConfMax_in" ∷ oldConfMax γ args.(AA_cn) args.(AA_log) ∗
       "#Hcommit_lb_in" ∷ commit_lb_by γ args.(AA_cn) (take (int.nat args.(AA_commitIdx)) args.(AA_log)) ∗
       "%HcommitLength" ∷ ⌜int.Z args.(AA_commitIdx) ≤ length args.(AA_log)⌝
  }}}
    ReplicaServer__AppendRPC #s #args_ptr
  {{{
       (r:bool), RET #r; ⌜r = true⌝ ∗ accepted_lb γ args.(AA_cn) rid args.(AA_log) ∨ ⌜r = false⌝
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  iNamed "HisRepl".
  wp_lam.
  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".

  wp_pures.
  iNamed "Hargs".
  (* First, deal with the replica step for appendRPC *)
  iNamed "Hrep".
  wp_loadField.
  wp_loadField.

  wp_if_destruct.
  { (* case: args.cn < s.cn *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "HmuInv Hlocked". iNext.
      do 6 iExists _.
      iFrame "∗#".
      iExists _; iFrame.
    }
    wp_pures.
    iApply "HΦ".
    iRight.
    done.
  }

  (* case: args.cn ≥ s.cn *)
  wp_loadField.
  wp_loadField.
  wp_apply (wp_or with "[HopLog HAlog]").
  { iNamedAccu. }
  { by wp_pures. }
  {
    iIntros "% HH"; iNamed "HH".
    wp_loadField.
    wp_apply (wp_slice_len).
    wp_loadField.
    wp_apply (wp_slice_len).
    wp_pures.
    by iFrame.
  }
  iNamed 1.

  iDestruct (is_slice_sz with "HopLog_slice") as %HopLogLen.
  iDestruct (is_slice_sz with "HAlog_slice") as %HALogLen.
  wp_apply (wp_If_join_evar with "[HopLog HopLog_slice Hcn HAlog HAlog_slice HAcn HrepG]").
  {
    iIntros.
    wp_if_destruct; last first.
    { (* won't grow log *)
      iMod (append_dup_ghost with "[$HrepG $Hproposal_lb_in]") as "[HrepG #Hacc]".
      { word. }

      iModIntro; iSplitL ""; first done.
      iAssert (∃ r',
                  "Hrep" ∷ own_Replica_phys s r' ∗
                  "HrepG" ∷ own_Replica_ghost rid γ r' ∗
                  "#Hacc" ∷ accepted_lb γ args.(AA_cn) rid args.(AA_log) ∗
                  "#HcommitterG_new" ∷ own_Committer_ghost γ r' c ∗
                  "%HlatestCn" ∷ ⌜r'.(cn) = args.(AA_cn)⌝
              )%I with "[HopLog HopLog_slice Hcn HrepG]" as "HH".
      {
        iExists _; iFrame "∗#". iSplitR "".
        { iExists _; iFrame. }
        iPureIntro.
        word.
      }
      iClear "HAlog HAcn HAlog_slice".
      iNamedAccu.
    }
    { (* will grow the log *)
      wp_loadField.
      wp_apply (wp_storeField with "HopLog").
      { apply slice_val_ty. }
      iIntros "HopLog".
      wp_pures.
      wp_loadField.
      wp_apply wp_fupd.
      wp_storeField.
      iSplitL ""; first done.
      iExists (mkReplica _ _).
      iSplitL "Hcn HopLog HAlog_slice".
      { (* re-establish own_Replica_phys *)
        iExists _. simpl. iFrame. done.
      }
      iMod (append_new_ghost with "[$HrepG $Hproposal_lb_in]") as "[$ #Hacc]".
      { word. }
      iMod (maintain_committer_ghost with "[$Hproposal_lb_in $HcommitterG]") as "$".
      { word. }
      { word. }
      iFrame "#".
      done.
    }
  }
  (* Done with replica step *)

  (* Do committer step *)
  iIntros "HH".
  wp_loadField.
  wp_loadField.

  wp_pures.
  iNamed "HH".
  iNamed "HH".
  wp_apply (wp_If_join_evar with "[Hcommitter HrepG HcommitterG HAcommitIdx]").
  {
    iIntros.
    wp_if_destruct.
    { (* args.commitIdx > commitIdx *)
      wp_loadField.
      iApply wp_fupd.
      wp_storeField.
      iSplitL ""; first done.
      iMod (commit_update with "[$HrepG HcommitterG Hacc Hcommit_lb_in]") as "[HrepG HcommitterG_final]".
      { done. }
      {
        rewrite HlatestCn.
        iFrame "#".
      }
      iAssert (∃ c', "Hcommitter" ∷ own_Committer_phys s r' c' ∗
                     "HcommiterG" ∷ own_Committer_ghost γ r' c'
              )%I with "[Hcommitter HcommitterG_final]" as "HH".
      {
        iExists (mkCommitterExtra _).
        iFrame.
      }
      iModIntro.
      iNamedAccu.
    }
    { (* args.commitIdx is not larger than commitIdx. boils down to the newly
         proposed value not contradicting the previously committed stuff, the
         proof is done earlier for conveneince. *)
        iModIntro. iSplitL ""; first done.
        iFrame.
        iExists _.
        iFrame.
        iFrame "#".
    }
  }
  (* Done with committer step.*)

  (* Now, release lock. *)
  iIntros "HH".
  iNamed "HH".
  iNamed "HH".
  wp_pures.
  wp_storeField.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    do 6 iExists _.
    iFrame "∗#".
  }
  wp_pures.
  iApply "HΦ".
  iLeft.
  iFrame "#".
  by iModIntro.
Qed.

Lemma wp_ReplicaServer__postAppendRPC (s:loc) (i:u64) conf rid γ (args_ptr:loc) args :
  {{{
       "#HisRepl" ∷ is_ReplicaServer s rid γ ∗
       "#Hconf" ∷ config_ptsto γ args.(AA_cn) conf ∗
       "%Hiconf" ∷ ⌜conf !! int.nat i = Some rid⌝ ∗
       "Hargs" ∷ own_AppendArgs args_ptr args ∗
       "#Hacc_lb" ∷ accepted_lb γ args.(AA_cn) rid args.(AA_log)
  }}}
    ReplicaServer__postAppendRPC #s #i #args_ptr
  {{{
       RET #(); True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_pures.

  iNamed "HisRepl".

  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  wp_pures.
  iNamed "Hown".
  iNamed "Hargs".

  (* First, deal with the replica step. *)
  iNamed "Hrep".
  wp_loadField.
  wp_loadField.
  wp_if_destruct; last first.
  {
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      do 6 iExists _. iFrame "∗ #".
      iExists _; iFrame.
    }
    wp_pures.
    by iApply "HΦ".
  }
  wp_loadField.
  assert (isPrimary = true) as ->.
  { admit. (* FIXME: have to add some extra monotonic ghost state to establish this *) }
  iNamed "Hown".
  iDestruct (config_ptsto_agree with "HconfPtsto Hconf") as %HconfAgree.
  rewrite HconfAgree.
  iDestruct (big_sepL2_lookup_1_some with "HmatchIdxAccepted") as %HmatchLookup.
  { done. }
  destruct HmatchLookup as [idx HmatchLookup].
  wp_apply (wp_SliceGet with "[$HmatchIdx_slice]").
  { done. }
  iIntros "HmatchIdx_slice".
  wp_loadField.
  wp_apply (wp_slice_len).
  iDestruct (is_slice_sz with "HopLog_slice") as %HopLogLen.
  wp_if_destruct.
  { (* increase matchIdx[i] *)
    wp_loadField.
    wp_apply (wp_slice_len).
    wp_loadField.
    wp_apply (wp_SliceSet with "[$HmatchIdx_slice]").
    { done. }
    iIntros "HmatchIdx_slice".
    wp_pures.
    wp_loadField.
    set matchIdx':=(<[int.nat i:=log_sl.(Slice.sz)]> matchIdx).
    wp_apply (wp_min with "[$HmatchIdx_slice]").
    iIntros (m) "(%Hm1&%Hm2&HmatchIdx_slice)".
    wp_pures.
    wp_loadField.
    wp_if_destruct.
    { (* commit something! *)
      wp_storeField.
      wp_loadField.

      wp_apply (release_spec with "[> -HΦ]").
      {
        iEval (rewrite -bi.later_intro).
        iFrame "HmuInv Hlocked".
        do 9 iExists _.
        iFrame "∗#".
        iFrame "HprimaryOwnsProposal".

        iSplitL "".
        {
          iMod (do_commit with "[]") as "$"; last done.
          iExists _; iFrame "#".
          (* FIXME: want to use x0 ∈ l to get resource out of [∗ list] x;y ∈ l;l', Φ x y *)
          iDestruct (big_sepL2_lookup_acc with "HmatchIdxAccepted") as "[HH _]".
          { done. }
          { done. }
          admit.
        }

        iSplitL "".
        { admit. (* use the fact that min ≤ matchIdx[0] ≤ length opLog or some such *) }
        iExists _; iFrame "#".
        iDestruct (big_sepL2_insert_acc with "HmatchIdxAccepted") as "HH".
        { done. }
        { done. }
        iFreeze "HH".
        replace (conf) with (<[int.nat i:=rid]> conf); last first.
        { by apply list_insert_id. }
        iThaw "HH".
        unfold matchIdx'.
        iDestruct "HH" as "[Hacc HH]".
        iApply "HH".
        admit. (* Show that take (len AA_log) opLog == args.(AA_log) by virtue of proposal_ptsto *)
      }
      wp_pures.
      by iApply "HΦ".
    }
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    {
      iEval (rewrite -bi.later_intro).
      iFrame "HmuInv Hlocked".
      do 9 iExists _.
      iFrame "∗#∗".
      iSplitL ""; first done.
      iExists _; iFrame "#".

      iFreeze "HmatchIdxAccepted".
      replace (conf) with (<[int.nat i:=rid]> conf); last first.
      { by apply list_insert_id. }
      iThaw "HmatchIdxAccepted".
      iDestruct (big_sepL2_insert_acc with "HmatchIdxAccepted") as "[_ HH]".
      { done. }
      { done. }
      iApply "HH".
      admit. (* Show that take (len AA_log) opLog == args.(AA_log) by virtue of proposal_ptsto *)
    }
    wp_pures.
    by iApply "HΦ".
  }
  {
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "HmuInv Hlocked".
      iNext. do 9 iExists _.
      iFrame "∗#∗".
      iSplitL ""; first done.
      iExists _; iFrame "#".
    }
    wp_pures.
    by iApply "HΦ".
  }
Admitted.

End append_proof.
