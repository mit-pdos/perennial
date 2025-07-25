From Perennial.program_proof.tulip Require Import prelude.

Lemma confined_by_ballot_map_inv_advance_absent
  {A} (bm : gmap nat ballot) (mm : gmap nat (gmap nat A)) ts l r x :
  bm !! ts = None ->
  (r ≤ length l)%nat ->
  confined_by_ballot_map bm mm ->
  confined_by_ballot_map (<[ts := l]> bm) (<[ts := {[r := x]}]> mm).
Proof.
  intros Hnone Hlen Hbm.
  apply map_Forall2_insert_2; last done.
  intros rx Hrx.
  rewrite lookup_insert_ne; first done.
  clear -Hlen Hrx. lia.
Qed.

Lemma confined_by_ballot_map_inv_advance_present
  {A} (bm : gmap nat ballot) (mm : gmap nat (gmap nat A)) ts l m r x :
  mm !! ts = Some m ->
  bm !! ts = Some l ->
  confined_by_ballot_map bm mm ->
  confined_by_ballot_map (<[ts := extend r Reject l]> bm) (<[ts := <[r := x]> m]> mm).
Proof.
  intros Hm Hl Hbm.
  apply map_Forall2_insert_2; last done.
  apply map_Forall2_forall in Hbm as [Hbm _].
  specialize (Hbm _ _ _ Hl Hm).
  intros rx Hrx.
  rewrite extend_length in Hrx.
  rewrite lookup_insert_ne; last lia.
  apply Hbm.
  lia.
Qed.

Definition advance_requirement st ts rk :=
  match st with
  | LocalState _ _ _ _ _ _ _ rkm =>
      match rkm !! ts with
      | Some n => (n < rk)%nat
      | _ => (O < rk)%nat
      end
  | _ => False
  end.

Definition last_accepted_decision st ts r p :=
  match st with
  | LocalState _ _ _ _ _ _ psm _ =>
      match psm !! ts with
      | Some psl => r = psl.1 ∧ p = psl.2
      | None => r = O ∧ p = false
      end
  | _ => False
  end.

Section advance.
  Context `{!tulip_ghostG Σ}.

  (* TODO: When this lemma is used for becoming the coordinator, [cid = (gid,
  rid)]. For use when receiving an inquire message, still need to figure out how
  [cid] is obtained. Worst case is to include them physically in the message. *)

  Lemma replica_inv_advance {γ gid rid clog ilog st} ts rk cid :
    execute_cmds (merge_clog_ilog clog ilog) = st ->
    advance_requirement st ts rk ->
    own_replica_clog_half γ gid rid clog -∗
    own_replica_ilog_half γ gid rid ilog -∗
    replica_inv_weak γ gid rid ==∗
    own_replica_clog_half γ gid rid clog ∗
    own_replica_ilog_half γ gid rid (ilog ++ [(length clog, CmdAdvance ts rk)]) ∗
    replica_inv γ gid rid ∗
    ([∗ set] tgid ∈ gids_all, own_replica_backup_token γ gid rid ts rk tgid) ∗
    is_replica_backup_vote γ gid rid ts rk cid ∗
    ∃ r p, prepare_promise γ gid rid ts rk r p ∗
           ⌜last_accepted_decision st ts r p⌝.
  Proof.
    iIntros (Hst Hrequire) "Hclogprog Hilogprog Hrp".
    do 2 iNamed "Hrp".
    (* Agreement on the consistent and inconsistent logs. *)
    iDestruct (replica_clog_agree with "Hclogprog Hclog") as %->.
    iDestruct (replica_ilog_agree with "Hilogprog Hilog") as %->.
    (* Update the inconsistent log. *)
    set ilog' := ilog ++ _.
    iMod (replica_ilog_update ilog' with "Hilogprog Hilog") as "[Hilogprog Hilog]".
    set st' := execute_advance st ts rk.
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
      rewrite /init_psm Hpsmts in Hrsm'.
      set blt' := extend rk Reject [Accept false].
      (* Insert [(ts, blt')] into the ballot map. *)
      iMod (replica_ballot_insert ts blt' with "Hblt") as "Hbm".
      { apply Hbmts. }
      set bm' := insert _ _ bm.
      (* Extract a witness that this replica accepts [false] at the fast rank. *)
      iDestruct (replica_ballot_witness ts with "Hbm") as "#Hlb".
      { by rewrite lookup_insert_eq. }
      iAssert (prepare_promise γ gid rid ts rk O false)%I as "#Hpromise".
      { iFrame "Hlb".
        subst blt'.
        rewrite latest_term_extend_Reject latest_term_singleton.
        iSplit; first done.
        iPureIntro.
        split.
        { rewrite lookup_extend_l; first done. simpl. lia. }
        { rewrite extend_length /=. rewrite Hrkmts in Hrequire. clear -Hrequire. lia. }
      }
      (* Vote for [cid] by inserting [(rk, cid)] into the submap of bvm. *)
      (* Insert [(ts, ∅)] into the backup vote map. *)
      iMod (replica_backup_vote_init ts with "Hbvm") as "Hbvm".
      { rewrite -not_elem_of_dom Hdombvm. by apply not_elem_of_dom in Hbmts. }
      (* And then insert [(rk, cid)] into the submap. *)
      iMod (replica_backup_vote_insert ts rk cid with "Hbvm") as "[Hbvm #Hvote]".
      { by rewrite lookup_insert_eq. }
      { done. }
      (* Obtain exclusive tokens for [cid] by inserting [(rk, cid)] into the submap of btm. *)
      (* Insert [(ts, ∅)] into the backup token map. *)
      iMod (replica_backup_token_init ts with "Hbtm") as "Hbtm".
      { rewrite -not_elem_of_dom Hdombtm. by apply not_elem_of_dom in Hbmts. }
      (* And then insert [(rk, gids_all)] into the submap. *)
      iMod (replica_backup_token_insert ts rk gids_all with "Hbtm") as "[Hbtm Hbts]".
      { by rewrite lookup_insert_eq. }
      { done. }
      iDestruct (big_sepM_insert_2 _ _ ts (O, false) with "[] Hfpw") as "Hfpw'".
      { rewrite /fast_proposal_witness /=.
        iFrame "Hlb".
        subst blt'.
        iPureIntro.
        rewrite lookup_extend_l; first done.
        simpl. lia.
      }
      iClear "Hfpw".
      iAssert (replica_inv_backup γ gid rid bm')%I with "[$Hbvm $Hbtm]" as "Hbackup".
      { iPureIntro.
        rewrite 5!dom_insert_L Hdombvm Hdombtm.
        do 2 (split; first set_solver).
        rewrite 2!insert_empty 2!insert_insert_eq.
        split.
        { apply confined_by_ballot_map_inv_advance_absent; [apply Hbmts | | apply Hbmbvm].
          rewrite extend_length /=.
          clear -Hrequire. lia.
        }
        { apply confined_by_ballot_map_inv_advance_absent; [apply Hbmts | | apply Hbmbtm].
          rewrite extend_length /=.
          clear -Hrequire. lia.
        }
      }
      iFrame "Hclogprog Hilogprog Hbackup Hpromise Hvote Hbts".
      iFrame "∗ # %".
      iModIntro.
      iSplit; last first.
      { iPureIntro.
        by rewrite /= Hpsmts.
      }
      iSplit.
      { iApply (big_sepM_insert_2 with "[] Hsafebm").
        subst blt'.
        iIntros (r).
        case_decide as Hr; first done.
        destruct (decide (rk ≤ r)%nat) as [Hge | Hlt].
        { rewrite lookup_ge_None_2; first done.
          rewrite extend_length /=.
          clear -Hr Hge. lia.
        }
        rewrite lookup_extend_r; first done.
        simpl.
        clear -Hr Hlt. lia.
      }
      iPureIntro.
      split.
      { apply Forall_app_2; [apply Hcloglen | by rewrite Forall_singleton]. }
      split.
      { apply map_Forall2_insert_2; last done.
        split; last done.
        by rewrite latest_term_extend_Reject latest_term_singleton.
      }
      { apply map_Forall2_insert_2; last done.
        rewrite extend_length /=.
        rewrite Hrkmts in Hrequire. clear -Hrequire. lia.
      }
    }
    assert (is_Some (psm !! ts)) as [psl Hpsmts].
    { apply map_Forall2_dom_L in Hbmpsm.
      by rewrite -elem_of_dom -Hbmpsm elem_of_dom.
    }
    assert (is_Some (rkm !! ts)) as [rl Hrkmts].
    { apply map_Forall2_dom_L in Hbmrkm.
      by rewrite -elem_of_dom -Hbmrkm elem_of_dom.
    }
    rewrite Hrkmts in Hrequire.
    rewrite /init_psm Hpsmts in Hrsm'.
    set blt' := extend rk Reject blt.
    (* Insert [(ts, blt')] into the ballot map. *)
    iMod (replica_ballot_update ts _ blt' with "Hblt") as "Hbm".
    { apply Hbmts. }
    { apply extend_prefix. }
    set bm' := insert _ _ bm.
    (* Extract a witness that this replica accepts [p] at the latest rank in [blt]. *)
    pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hbmts Hpsmts Hbmpsm) as [Hpsl1 Hpsl2].
    pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hbmts Hrkmts Hbmrkm) as Hlenblt.
    simpl in Hlenblt. subst rl.
    iAssert (prepare_promise γ gid rid ts rk psl.1 psl.2)%I as "#Hpromise".
    { iDestruct (replica_ballot_witness ts with "Hbm") as "#Hlb".
      { by rewrite lookup_insert_eq. }
      iFrame "Hlb".
      subst blt'.
      rewrite latest_term_extend_Reject.
      iSplit.
      { rewrite /is_group_prepare_proposal_if_classic.
        case_decide as Hnz; first done.
        iDestruct (big_sepM_lookup with "Hsafebm") as "Hsafeblt"; first apply Hbmts.
        iSpecialize ("Hsafeblt" $! (latest_term blt)).
        case_decide as Hnz'.
        { rewrite Hnz' in Hpsl1. clear -Hnz Hpsl1. word. }
        by rewrite Hpsl1 Hpsl2.
      }
      iPureIntro.
      split.
      { rewrite lookup_extend_l; first done.
        rewrite -Hpsl1.
        apply latest_term_length_lt.
        by intros ->.
      }
      { rewrite extend_length Hpsl1.
        clear -Hrequire. lia.
      }
    }
    (* Vote for [cid] by inserting [(rk, cid)] into the submap of bvm. *)
    assert (is_Some (bvm !! ts)) as [bvmts Hbvmts].
    { by rewrite -elem_of_dom Hdombvm elem_of_dom. }
    iMod (replica_backup_vote_insert ts rk cid with "Hbvm") as "[Hbvm #Hvote]".
    { apply Hbvmts. }
    { apply map_Forall2_forall in Hbmbvm as [Hbmbvm _].
      specialize (Hbmbvm _ _ _ Hbmts Hbvmts).
      apply Hbmbvm.
      clear -Hrequire. lia.
    }
    (* Obtain exclusive tokens for [cid] by inserting [(rk, cid)] into the submap of btm. *)
    assert (is_Some (btm !! ts)) as [btmts Hbtmts].
    { by rewrite -elem_of_dom Hdombtm elem_of_dom. }
    iMod (replica_backup_token_insert ts rk gids_all with "Hbtm") as "[Hbtm Hbts]".
    { apply Hbtmts. }
    { apply map_Forall2_forall in Hbmbtm as [Hbmbtm _].
      specialize (Hbmbtm _ _ _ Hbmts Hbtmts).
      apply Hbmbtm, Hrequire.
    }
    iAssert (replica_inv_backup γ gid rid bm')%I with "[$Hbvm $Hbtm]" as "Hbackup".
    { iPureIntro.
      rewrite 3!dom_insert_L Hdombvm Hdombtm.
      do 2 (split; first done).
      split; by eapply confined_by_ballot_map_inv_advance_present.
    }
    iFrame "Hclogprog Hilogprog Hbackup Hpromise Hvote Hbts".
    iFrame "∗ # %".
    iModIntro.
    iSplit; last first.
    { iPureIntro. by rewrite /= Hpsmts. }
    iSplit.
    { iApply (big_sepM_insert_2 with "[] Hsafebm").
      subst blt'.
      iIntros (r).
      case_decide as Hr; first done.
      destruct (decide (rk ≤ r)%nat) as [Hge | Hlt].
      { rewrite lookup_ge_None_2; first done.
        rewrite extend_length /=.
        clear -Hrequire Hge. lia.
      }
      destruct (decide (length blt ≤ r)%nat) as [Hgelen | Hltlen].
      { rewrite lookup_extend_r; first done.
        clear -Hgelen Hlt. lia.
      }
      rewrite lookup_extend_l; last first.
      { clear -Hltlen. lia. }
      iDestruct (big_sepM_lookup with "Hsafebm") as "Hsafeblt"; first apply Hbmts.
      iSpecialize ("Hsafeblt" $! r).
      by case_decide.
    }
    iPureIntro.
    split.
    { apply Forall_app_2; [apply Hcloglen | by rewrite Forall_singleton]. }
    split.
    { rewrite -(insert_id _ _ _ Hpsmts).
      apply map_Forall2_insert_2; last done.
      subst blt'.
      split.
      { by rewrite latest_term_extend_Reject Hpsl1. }
      { rewrite lookup_extend_l; first done.
        by eapply lookup_lt_Some.
      }
    }
    { apply map_Forall2_insert_2; last done.
      subst blt'.
      rewrite extend_length.
      clear -Hrequire. lia.
    }
  Qed.

End advance.
