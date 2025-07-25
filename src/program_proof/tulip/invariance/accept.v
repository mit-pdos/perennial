From Perennial.program_proof.tulip Require Import prelude.

Lemma confined_by_ballot_map_inv_accept_absent
  {A} (bm : gmap nat ballot) (mm : gmap nat (gmap nat A)) ts l :
  bm !! ts = None ->
  confined_by_ballot_map bm mm ->
  confined_by_ballot_map (<[ts := l]> bm) (<[ts := ∅]> mm).
Proof. intros Hnone Hbm. by apply map_Forall2_insert_2. Qed.

Lemma confined_by_ballot_map_inv_accept_present
  {A} (bm : gmap nat ballot) (mm : gmap nat (gmap nat A)) ts l l' :
  bm !! ts = Some l ->
  prefix l l' ->
  confined_by_ballot_map bm mm ->
  confined_by_ballot_map (<[ts := l']> bm) mm.
Proof.
  intros Hl Hprefix Hbm.
  rewrite /confined_by_ballot_map map_Forall2_forall.
  split; last first.
  { apply map_Forall2_dom_L in Hbm.
    rewrite dom_insert_L Hbm.
    apply elem_of_dom_2 in Hl.
    set_solver.
  }
  apply map_Forall2_forall in Hbm as [Hbm _].
  intros t k m Hk Hm.
  destruct (decide (t = ts)) as [-> | Hne]; last first.
  { rewrite lookup_insert_ne in Hk; last done.
    by eapply Hbm.
  }
  rewrite lookup_insert_eq in Hk. inv Hk.
  intros r Hlen.
  specialize (Hbm _ _ _ Hl Hm r).
  apply Hbm.
  apply prefix_length in Hprefix.
  clear -Hlen Hprefix. lia.
Qed.

Definition accept_requirement st ts rk :=
  match st with
  | LocalState _ _ _ _ _ _ _ rkm =>
      match rkm !! ts with
      | Some r => (r ≤ rk)%nat
      | _ => True
      end
  | _ => False
  end.

Section accept.
  Context `{!tulip_ghostG Σ}.

  Lemma replica_inv_accept {γ gid rid clog ilog st} ts rk p :
    execute_cmds (merge_clog_ilog clog ilog) = st ->
    accept_requirement st ts rk ->
    (if decide (rk = O)
     then (if p : bool then is_replica_validated_ts γ gid rid ts else True)
     else is_group_prepare_proposal γ gid ts rk p) -∗
    own_replica_clog_half γ gid rid clog -∗
    own_replica_ilog_half γ gid rid ilog -∗
    replica_inv_weak γ gid rid ==∗
    own_replica_clog_half γ gid rid clog ∗
    own_replica_ilog_half γ gid rid (ilog ++ [(length clog, CmdAccept ts rk p)]) ∗
    replica_inv γ gid rid ∗
    is_replica_pdec_at_rank γ gid rid ts rk p.
  Proof.
    iIntros (Hst Hrequire) "#Hpsl Hclogprog Hilogprog Hrp".
    do 2 iNamed "Hrp".
    (* Agreement on the consistent and inconsistent logs. *)
    iDestruct (replica_clog_agree with "Hclogprog Hclog") as %->.
    iDestruct (replica_ilog_agree with "Hilogprog Hilog") as %->.
    (* Update the inconsistent log. *)
    set ilog' := ilog ++ _.
    iMod (replica_ilog_update ilog' with "Hilogprog Hilog") as "[Hilogprog Hilog]".
    set st' := execute_accept st ts rk p.
    (* This will evaluate to the right form to re-establish the RSM invariant. *)
    assert (Hrsm' : execute_cmds (merge_clog_ilog clog ilog') = st').
    { rewrite merge_clog_ilog_snoc_ilog; last done.
      by rewrite execute_cmds_snoc Hst /=.
    }
    destruct st as [cmx histmx cpmx ptgsmx sptsmx ptsmx psmx rkmx |]; last done.
    simpl in Hrequire.
    rewrite Hrsm in Hst. symmetry in Hst. inv Hst.
    iNamed "Hbackup".
    iNamed "Hbm".
    simpl in Hrsm'.
    (* Establish [eq_lsn_last_ilog (length clog) ilog'] with [ge_lsn_last_ilog ...]. *)
    assert (Heqlast' : eq_lsn_last_ilog (length clog) ilog').
    { by rewrite /eq_lsn_last_ilog last_snoc. }
    (* Re-establish [ilog_lsn_sorted ilog']. *)
    assert (Hisorted' : ilog_lsn_sorted ilog').
    { apply ilog_lsn_sorted_inv_snoc; [apply Heqlast | apply Hisorted]. }
    destruct (bm !! ts) as [blt |] eqn:Hbmts; last first.
    { (* Case: [bm !! ts = None]. *)
      assert (Hpsmts : psm !! ts = None).
      { apply map_Forall2_dom_L in Hbmpsm.
        by rewrite -not_elem_of_dom -Hbmpsm not_elem_of_dom.
      }
      assert (Hrkmts : rkm !! ts = None).
      { apply map_Forall2_dom_L in Hbmrkm.
        by rewrite -not_elem_of_dom -Hbmrkm not_elem_of_dom.
      }
      set blt' := replicate rk Reject ++ [Accept p].
      (* Insert [(ts, blt')] into the ballot map. *)
      iMod (replica_ballot_insert ts blt' with "Hblt") as "Hbm".
      { apply Hbmts. }
      set bm' := insert _ _ bm.
      (* Extract a witness that this replica accepts [p] at the rank [rk]. *)
      iAssert (is_replica_pdec_at_rank γ gid rid ts rk p)%I as "#Hblt".
      { iDestruct (replica_ballot_witness ts with "Hbm") as "#Hlb".
        { by rewrite lookup_insert_eq. }
        iFrame "Hlb".
        iPureIntro.
        rewrite lookup_snoc_Some.
        right.
        by rewrite length_replicate.
      }
      (* Insert [(ts, ∅)] into the backup vote map. *)
      iMod (replica_backup_vote_init ts with "Hbvm") as "Hbvm".
      { rewrite -not_elem_of_dom Hdombvm. by apply not_elem_of_dom in Hbmts. }
      (* Insert [(ts, ∅)] into the backup token map. *)
      iMod (replica_backup_token_init ts with "Hbtm") as "Hbtm".
      { rewrite -not_elem_of_dom Hdombtm. by apply not_elem_of_dom in Hbmts. }
      iDestruct (big_sepM_insert_2 _ _ ts (rk, p) with "[] Hfpw") as "Hfpw'".
      { rewrite /fast_proposal_witness /=.
        case_decide as Hz; last done. subst rk.
        destruct p; iFrame "#".
      }
      iClear "Hfpw".
      iAssert (replica_inv_backup γ gid rid bm')%I with "[$Hbvm $Hbtm]" as "Hbackup".
      { iPureIntro.
        rewrite 3!dom_insert_L Hdombvm Hdombtm.
        do 2 (split; first done).
        by split; apply confined_by_ballot_map_inv_accept_absent.
      }
      iFrame "Hclogprog Hilogprog Hbackup Hblt".
      iFrame "∗ # %".
      iModIntro.
      iSplit.
      { iApply (big_sepM_insert_2 with "[] Hsafebm").
        subst blt'.
        iIntros (r).
        case_decide as Hrk.
        { case_decide as Hr; first done.
          rewrite Hrk /= lookup_ge_None_2; first done.
          simpl. clear -Hr. lia.
        }
        case_decide as Hr; first done.
        destruct (_ !! r) as [v |] eqn:Hv; last done.
        rewrite lookup_snoc_Some in Hv.
        destruct Hv as [[_ Hrej] | [Hlen <-]].
        { by apply lookup_replicate in Hrej as [-> _]. }
        rewrite length_replicate in Hlen. by inv Hlen.
      }
      iPureIntro.
      split.
      { apply Forall_app_2; [apply Hcloglen | by rewrite Forall_singleton]. }
      split.
      { apply map_Forall2_insert_2; last done.
        rewrite /= latest_term_snoc_Accept length_replicate.
        split; first done.
        by rewrite lookup_snoc_length'; last rewrite length_replicate.
      }
      { apply map_Forall2_insert_2; last done.
        rewrite length_app /= length_replicate.
        lia.
      }
    }
    (* Case: [bm !! ts = Some blt]. *)
    assert (is_Some (psm !! ts)) as [psl Hpsmts].
    { apply map_Forall2_dom_L in Hbmpsm.
      by rewrite -elem_of_dom -Hbmpsm elem_of_dom.
    }
    assert (is_Some (rkm !! ts)) as [rl Hrkmts].
    { apply map_Forall2_dom_L in Hbmrkm.
      by rewrite -elem_of_dom -Hbmrkm elem_of_dom.
    }
    rewrite Hrkmts in Hrequire.
    set blt' := extend rk Reject blt ++ [Accept p].
    (* Update the ballot map with [(ts, blt')]. *)
    iMod (replica_ballot_update ts _ blt' with "Hblt") as "Hbm".
    { apply Hbmts. }
    { by apply prefix_app_r, extend_prefix. }
    set bm' := insert _ _ bm.
    pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hbmts Hrkmts Hbmrkm) as Hlenblt.
    simpl in Hlenblt. subst rl.
    (* Extract a witness that this replica accepts [p] at the fast rank. *)
    iAssert (is_replica_pdec_at_rank γ gid rid ts rk p)%I as "#Hblt".
    { iDestruct (replica_ballot_witness ts with "Hbm") as "#Hlb".
      { by rewrite lookup_insert_eq. }
      iFrame "Hlb".
      iPureIntro.
      rewrite lookup_snoc_Some.
      right.
      rewrite extend_length.
      split; last done.
      clear -Hrequire. lia.
    }
    iDestruct (big_sepM_insert_2 _ _ ts (rk, p) with "[] Hfpw") as "Hfpw'".
    { rewrite /fast_proposal_witness /=.
      case_decide as Hz; last done. subst rk.
      destruct p; iFrame "#".
    }
    iClear "Hfpw".
    iAssert (replica_inv_backup γ gid rid bm')%I with "[$Hbvm $Hbtm]" as "Hbackup".
    { iPureIntro.
      rewrite dom_insert_L Hdombvm Hdombtm.
      apply elem_of_dom_2 in Hbmts as Hin.
      do 2 (split; first set_solver).
      assert (Hprefix : prefix blt blt').
      { apply prefix_app_r, extend_prefix. }
      split; by eapply confined_by_ballot_map_inv_accept_present.
    }
    iFrame "Hclogprog Hilogprog Hbackup Hblt".
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { iApply (big_sepM_insert_2 with "[] Hsafebm").
      subst blt'.
      iIntros (r).
      case_decide as Hrk.
      { subst rk.
        case_decide as Hr; first done.
        rewrite /= /extend /= app_nil_r lookup_ge_None_2; first done.
        assert (Hblt : length blt = O).
        { clear -Hrequire. lia. }
        apply nil_length_inv in Hblt as ->.
        simpl. clear -Hr. lia.
      }
      case_decide as Hr; first done.
      destruct (decide (rk < r)%nat) as [Hgt | Hle].
      { rewrite lookup_ge_None_2; first done.
        rewrite length_app /= extend_length.
        clear -Hrequire Hgt. lia.
      }
      apply Nat.nlt_ge in Hle.
      destruct (decide (rk = r)) as [-> | Hne].
      { rewrite lookup_snoc_length'; first done.
        rewrite extend_length. clear -Hrequire. lia.
      }
      assert (Hlt : (r < rk)%nat) by lia.
      rewrite lookup_app_l; last first.
      { rewrite extend_length. clear -Hrequire Hlt. lia. }
      destruct (decide (length blt ≤ r)%nat) as [Hgelen | Hltlen].
      { rewrite lookup_extend_r; first done.
        clear -Hlt Hgelen. lia.
      }
      apply Nat.nle_gt in Hltlen.
      rewrite lookup_extend_l; last apply Hltlen.
      iDestruct (big_sepM_lookup with "Hsafebm") as "Hsafeblt"; first apply Hbmts.
      iSpecialize ("Hsafeblt" $! r).
      by case_decide.
    }
    iPureIntro.
    split.
    { apply Forall_app_2; [apply Hcloglen | by rewrite Forall_singleton]. }
    split.
    { apply map_Forall2_insert_2; last done.
      rewrite /= latest_term_snoc_Accept extend_length.
      split.
      { clear -Hrequire. lia. }
      rewrite lookup_snoc_length'; first done.
      rewrite extend_length.
      clear -Hrequire. lia.
    }
    { apply map_Forall2_insert_2; last done.
      rewrite length_app /= extend_length.
      clear -Hrequire. lia.
    }
  Qed.

End accept.
