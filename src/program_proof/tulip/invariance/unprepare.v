From Perennial.program_proof.tulip Require Import prelude.
From Perennial.program_proof.tulip.invariance Require Import prepare.

Section inv.
  Context `{!heapGS Σ}.
  Context `{!tulip_ghostG Σ}.

  Lemma txnsys_group_inv_unprepare γ p gid ts pwrs :
    quorum_unprepared γ gid ts -∗
    safe_txn_pwrs γ gid ts pwrs -∗
    ([∗ set] rid ∈ rids_all, replica_inv γ gid rid) -∗
    group_inv γ gid -∗
    txnsys_inv γ p ==∗
    ([∗ set] rid ∈ rids_all, replica_inv γ gid rid) ∗
    group_inv γ gid ∗
    txnsys_inv γ p ∗
    is_txn_aborted γ ts.
  Proof.
    iIntros "#Hqn #Hpwrs Hrps Hgroup Htxnsys".
    do 2 iNamed "Htxnsys".
    destruct (resm !! ts) as [res |] eqn:Hres.
    { destruct res as [wrs |].
      { (* Case: Txn [ts] committed. Derive contradiction. *)
        iDestruct (big_sepM_lookup with "Hvr") as "Hr"; first apply Hres.
        simpl.
        iDestruct "Hr" as "[Hwrs Hgps]".
        iDestruct "Hpwrs" as (wrs') "[Hwrs' %Hpwrs]".
        iDestruct (txn_wrs_agree with "Hwrs Hwrs'") as %->.
        destruct Hpwrs as (Hvts & Hvwrs & Hne & Hwg).
        pose proof (wrs_group_elem_of_ptgroups _ _ _ Hne Hwg) as Hgid.
        iDestruct (big_sepS_elem_of with "Hgps") as "Hgp"; first apply Hgid.
        do 2 iNamed "Hgroup".
        iDestruct (group_prep_lookup with "Hpm Hgp") as %Hgp.
        iDestruct (big_sepM_lookup with "Hsafepm") as "Hqp"; first apply Hgp.
        iDestruct "Hqp" as "[Hqp _]".
        iDestruct (not_quorum_prepared_unprepared with "Hqp Hqn Hrps Hpsm") as %[].
      }
      (* Case: Txn [ts] aborted. Extract witness without updates. *)
      iDestruct (txn_res_witness with "Hresm") as "#Habted"; first apply Hres.
      by iFrame "Hrps Hgroup ∗ # %".
    }
    (* Case: Txn [ts] not finalized. *)
    do 2 iNamed "Hgroup".
    destruct (stm !! ts) as [st |] eqn:Hst.
    { (* Case: Txn [ts] has prepared, committed, or aborted on group [gid]. Contradiction. *)
      iDestruct (big_sepM_lookup with "Hsafestm") as "Hsafest"; first apply Hst.
      destruct st as [pwrs' | |].
      { (* Case: Prepared. Contradiction from stability. *)
        iDestruct "Hsafest" as "[Hgp _]".
        iDestruct (group_prep_lookup with "Hpm Hgp") as %Hgp.
        iDestruct (big_sepM_lookup with "Hsafepm") as "Hsafep"; first apply Hgp.
        iDestruct "Hsafep" as "[Hqp _]".
        iDestruct (not_quorum_prepared_unprepared with "Hqp Hqn Hrps Hpsm") as %[].
      }
      { (* Case: Committed. Contradiction from the fact that [ts] has not finalized globally. *)
        iDestruct "Hsafest" as (wrs) "Hwrs".
        iDestruct (txn_res_lookup with "Hresm Hwrs") as %Hcmted.
        by rewrite Hres in Hcmted.
      }
      { (* Case: Aborted. Contradiction from the fact that [ts] has not finalized globally. *)
        iDestruct (txn_res_lookup with "Hresm Hsafest") as %Habted.
        by rewrite Hres in Habted.
      }
    }
    (* Insert [(ts, ResAborted)] into the txn result map. *)
    iMod (txn_res_insert ts ResAborted with "Hresm") as "Hresm"; first apply Hres.
    iDestruct (txn_res_witness ts with "Hresm") as "#Habted".
    { by rewrite lookup_insert_eq. }
    (* Re-establish group invariant. *)
    iAssert (|==> group_inv γ gid ∗ is_group_unprepared γ gid ts)%I
      with "[Hlog Hcpool Hpm Hcm Hhists Hlocks Hpsm]" as "Hgroupgnp".
    { destruct (pm !! ts) as [b |] eqn:Hpm.
      { destruct b.
        { exfalso.
          apply not_elem_of_dom in Hst.
          clear -Hpmstm Hst Hpm.
          by specialize (Hpmstm _ _ Hpm).
        }
        iDestruct (group_prep_witness with "Hpm") as "#Hgnp"; first apply Hpm.
        by iFrame "∗ # %".
      }
      (* Insert [(ts, false)] into the group prepare map. *)
      iMod (group_prep_insert ts false with "Hpm") as "[Hpm Hgnp]"; first apply Hpm.
      iFrame "∗ # %".
      iModIntro.
      iSplit.
      { iApply (big_sepM_insert_2 with "[] Hsafepm"). iFrame "Hqn". }
      iPureIntro.
      intros t b Hb.
      destruct (decide (t = ts)) as [-> | Hne]; last first.
      { rewrite lookup_insert_ne in Hb; last done. by specialize (Hpmstm _ _ Hb). }
      rewrite lookup_insert_eq in Hb.
      by inv Hb.
    }
    iMod "Hgroupgnp" as "[Hgroup #Hgnp]".
    iFrame "Hrps Hgroup ∗ # %".
    iModIntro.
    iSplitL "Hpart".
    { iNamed "Hpart".
      rewrite /partitioned_tids resm_to_tmods_insert_aborted; last by left.
      iFrame.
      iPureIntro.
      intros tid Htid.
      specialize (Hfate _ Htid). simpl in Hfate.
      set_solver.
    }
    rewrite resm_to_tmods_insert_aborted; last by left.
    iFrame "Hkmodcs".
    iSplit.
    { iApply (big_sepM_insert_2 with "[] Hvr").
      iLeft.
      iDestruct "Hpwrs" as (wrs) "[Hwrs %Hwrs]".
      iFrame "Hgnp Hwrs".
      iPureIntro.
      destruct Hwrs as (_ & _ & Hne & Hwg).
      by eapply wrs_group_elem_of_ptgroups.
    }
    iPureIntro.
    split.
    { apply (map_Forall_impl _ _ _ Htidcs).
      intros t m Htm.
      destruct Htm as [? | Htm]; first by left.
      right.
      rewrite lookup_insert_ne; first done.
      intros ->.
      by rewrite Hres in Htm.
    }
    { by rewrite /cmtxn_in_past resm_to_tmods_insert_aborted; last by left. }
  Qed.

End inv.
