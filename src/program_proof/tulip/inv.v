From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm Require Import big_sep.
From Perennial.program_proof.rsm.pure Require Import vslice extend quorum fin_maps.
From Perennial.program_proof.tulip Require Import base res cmd.
From Perennial.program_proof.tulip Require Export inv_txnsys inv_key inv_group inv_replica.

Section inv.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  Definition sysNS := nroot .@ "sys".
  Definition tulipNS := sysNS .@ "tulip".
  Definition tsNS := sysNS .@ "ts".

  Definition tulip_inv γ p : iProp Σ :=
    (* txn invariants *)
    "Htxnsys"   ∷ txnsys_inv γ p ∗
    (* keys invariants *)
    "Hkeys"     ∷ ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    (* groups invariants *)
    "Hgroups"   ∷ ([∗ set] gid ∈ gids_all, group_inv γ gid) ∗
    (* replica invariants *)
    "Hreplicas" ∷ ([∗ set] gid ∈ gids_all, [∗ set] rid ∈ rids_all, replica_inv γ gid rid).

  #[global]
  Instance tulip_inv_timeless γ p :
    Timeless (tulip_inv γ p).
  Admitted.

  Definition know_tulip_inv γ p : iProp Σ :=
    inv tulipNS (tulip_inv γ p).

End inv.

Section alloc.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Lemma tulip_inv_alloc p future :
    own_txn_proph p future ==∗
    ∃ γ,
      (* give to client *)
      ([∗ set] k ∈ keys_all, own_db_ptsto γ k None) ∗
      (* give to replica lock invariant *)
      ([∗ set] g ∈ gids_all, [∗ set] r ∈ rids_all,
         own_replica_clog_half γ g r [] ∗ own_replica_ilog_half γ g r []) ∗
      (* tulip atomic invariant *)
      tulip_inv γ p.
  Proof.
    iIntros "Hproph".
    iMod (tulip_res_alloc) as (γ) "Hres".
    iDestruct "Hres" as "(Hcli & Hresm & Hwrsm & Hltids & Hwabt & Htmods & Hres)".
    iDestruct "Hres" as "(Hexcltids & Hexclctks & Hpost & Hlts & Hres)".
    iDestruct "Hres" as "(Hdbpts & Hrhistmg & Hrhistmk & Hrtsg & Hrtsk & Hres)".
    iDestruct "Hres" as "(Hchistm & Hlhistm & Hkmodlst & Hkmodlsk & Hkmodcst & Hkmodcsk & Hres)".
    iDestruct "Hres" as "(Hlogs & Hcpools & Hpms & Hpsms & Hcms & Hrps & Hrplocks)".
    (* Obtain a lb on the largest timestamp to later establish group invariant. *)
    iDestruct (largest_ts_witness with "Hlts") as "#Hltslb".
    iAssert (txnsys_inv γ p)
      with "[Hproph Hresm Hwrsm Hltids Hwabt Htmods Hexcltids Hexclctks Hpost Hlts Hkmodlst Hkmodcst]"
      as "Htxnsys".
    { iFrame.
      (* Instantiate past actions, linearized txn modifications. *)
      iExists [], ∅, ∅.
      iSplitR.
      { by rewrite /partitioned_tids 3!dom_empty_L big_sepS_empty. }
      iSplitL "Hkmodlst".
      { iApply (big_sepS_mono with "Hkmodlst").
        iIntros (k).
        by rewrite vslice_empty.
      }
      iSplitL "Hkmodcst".
      { iApply (big_sepS_mono with "Hkmodcst").
        iIntros (k).
        by rewrite vslice_empty.
      }
      rewrite /wrsm_dbmap omap_empty 3!big_sepM_empty big_sepL_nil.
      do 4 (iSplit; first done).
      iPureIntro.
      by rewrite !dom_empty_L /conflict_past.
    }
    iAssert ([∗ set] key ∈ keys_all, quorum_invalidated_key γ key O)%I as "#Hqiks".
    { iApply big_sepS_forall.
      iIntros (k Hk).
      iExists rids_all.
      iSplit; last first.
      { iPureIntro. apply cquorum_refl.
        rewrite /rids_all size_list_to_set; last first.
        { apply seq_U64_NoDup; lia. }
        rewrite length_fmap length_seqZ.
        lia.
      }
      pose proof (elem_of_key_to_group k) as Hin.
      iDestruct (big_sepS_elem_of with "Hrps") as "Hrp"; first apply Hin.
      iDestruct "Hrp" as "(_ & Hkvls & _)".
      iApply (big_sepS_mono with "Hkvls").
      iIntros (rid Hrid) "Hkvl".
      iDestruct (big_sepS_elem_of with "Hkvl") as "Hk"; first apply Hk.
      iDestruct (replica_key_validation_witness with "Hk") as "#Hik".
      by iFrame "Hik".
    }
    iAssert ([∗ set] key ∈ keys_all, key_inv γ key)%I
      with "[Hdbpts Hrhistmk Hrtsk Hchistm Hlhistm Hkmodlsk Hkmodcsk]" as "Hkeys".
    { iDestruct (big_sepS_sep_2 with "Hkmodlsk Hkmodcsk") as "Hkeys".
      iDestruct (big_sepS_sep_2 with "Hlhistm Hkeys") as "Hkeys".
      iDestruct (big_sepS_sep_2 with "Hchistm Hkeys") as "Hkeys".
      iDestruct (big_sepS_sep_2 with "Hrtsk Hkeys") as "Hkeys".
      iDestruct (big_sepS_sep_2 with "Hrhistmk Hkeys") as "Hkeys".
      iDestruct (big_sepS_sep_2 with "Hdbpts Hkeys") as "Hkeys".
      iApply (big_sepS_impl with "Hkeys").
      iIntros (k Hk) "!> (Hdbpts & Hrhistmk & Hrtsk & Hchistm & Hlhistm & Hkmodlsk & Hkmodcsk)".
      iFrame.
      (* Instantiate largest timestamp seen in this key. *)
      iExists O.
      iSplit.
      { iDestruct (big_sepS_elem_of with "Hqiks") as "Hqik"; first apply Hk.
        iDestruct "Hqik" as (ridsq) "[Hkvls %Hquorum]".
        iExists ridsq.
        iSplit; last done.
        iApply (big_sepS_mono with "Hkvls").
        iIntros (rid Hrid) "Hkvl".
        iDestruct "Hkvl" as (l) "[Hlb %Hinvalid]".
        iFrame "Hlb".
        iPureIntro.
        apply lookup_lt_Some in Hinvalid.
        simpl. lia.
      }
      iSplit.
      { rewrite /committed_or_quorum_invalidated_key lookup_empty.
        iLeft.
        iDestruct (big_sepS_elem_of with "Hqiks") as "Hqik"; first apply Hk.
        iDestruct "Hqik" as (ridsq) "[Hkvls %Hquorum]".
        iExists ridsq.
        iSplit; last done.
        iApply (big_sepS_mono with "Hkvls").
        iIntros (rid Hrid) "Hkvl".
        iDestruct "Hkvl" as (l) "[Hlb %Hinvalid]".
        by iFrame "Hlb".
      }
      iSplit; first by iApply big_sepM_empty.
      iSplit; first done.
      iPureIntro.
      assert (Hextl : ext_by_lnrz [None] [None] ∅).
      { exists None.
        split; first done.
        split; first done.
        rewrite dom_empty_L.
        split; first done.
        intros t u _ Hu.
        apply list_lookup_singleton_Some in Hu as [_ <-].
        by rewrite prev_dbval_empty.
      }
      assert (Hextc : ext_by_cmtd [None] [None] ∅ O).
      { rewrite /ext_by_cmtd lookup_empty.
        exists O.
        split; last done.
        rewrite last_extend_id; first done.
        simpl. lia.
      }
      assert (Hyield : cmtd_yield_from_kmodc [None] ∅).
      { intros t Ht. simpl in Ht.
        assert (t = O) as -> by lia.
        by rewrite prev_dbval_empty.
      }
      done.
    }
    (* Obtain lower bounds on the transaction log to later establish replica invariant. *)
    iAssert ([∗ set] gid ∈ gids_all, is_txn_log_lb γ gid [])%I as "#Hloglbs".
    { iApply (big_sepS_mono with "Hlogs").
      iIntros (gid Hgid) "Hlog".
      by iApply txn_log_witness.
    }
    iAssert ([∗ set] gid ∈ gids_all, group_inv γ gid)%I
      with "[Hrhistmg Hrtsg Hlogs Hcpools Hpms Hpsms Hcms]" as "Hgroups".
    { set f := λ k g, key_to_group k = g.
      iDestruct (big_sepS_partition_1 _ _ gids_all f with "Hrhistmg") as "Hrhistmg".
      { intros k g1 g2 Hne Hpos Hneg. subst f. by rewrite Hpos in Hneg. }
      iDestruct (big_sepS_partition_1 _ _ gids_all f with "Hrtsg") as "Hrtsg".
      { intros k g1 g2 Hne Hpos Hneg. subst f. by rewrite Hpos in Hneg. }
      iDestruct (big_sepS_sep_2 with "Hpsms Hcms") as "Hgroups".
      iDestruct (big_sepS_sep_2 with "Hpms Hgroups") as "Hgroups".
      iDestruct (big_sepS_sep_2 with "Hcpools Hgroups") as "Hgroups".
      iDestruct (big_sepS_sep_2 with "Hlogs Hgroups") as "Hgroups".
      iDestruct (big_sepS_sep_2 with "Hrtsg Hgroups") as "Hgroups".
      iDestruct (big_sepS_sep_2 with "Hrhistmg Hgroups") as "Hgroups".
      iApply (big_sepS_mono with "Hgroups").
      iIntros (gid Hgid) "(Hrhistmg & Hrtsg & Hlogs & Hcpools & Hpms & Hpsms & Hcms)".
      iFrame.
      (* Instantiate the status map, history map, and lock map. *)
      iExists ∅, (gset_to_gmap [None] keys_all), (gset_to_gmap O keys_all).
      iSplitL "Hrhistmg".
      { iApply (big_sepS_sepM_impl with "Hrhistmg").
        { by rewrite filter_group_keys_group_dom dom_gset_to_gmap. }
        iIntros (k h Hh) "!> Hhist".
        apply map_lookup_filter_Some_1_1 in Hh.
        by apply lookup_gset_to_gmap_Some in Hh as [_ <-].
      }
      iSplitL "Hrtsg".
      { iApply (big_sepS_sepM_impl with "Hrtsg").
        { by rewrite filter_group_keys_group_dom dom_gset_to_gmap. }
        iIntros (k t Ht) "!> Hts".
        apply map_lookup_filter_Some_1_1 in Ht.
        by apply lookup_gset_to_gmap_Some in Ht as [_ <-].
      }
      rewrite !big_sepM_empty big_sepS_empty.
      iSplit; first done.
      do 3 (iSplit; first done).
      iPureIntro.
      rewrite dom_gset_to_gmap.
      assert (Hlip : locked_impl_prepared ∅ (gset_to_gmap O keys_all)).
      { intros k t Ht Hnz. by apply lookup_gset_to_gmap_Some in Ht as [_ <-]. }
      done.
    }
    iAssert ([∗ set] gid ∈ gids_all, [∗ set] rid ∈ rids_all, replica_inv γ gid rid)%I
      with "[Hrps]" as "Hrps".
    { iApply (big_sepS_impl with "Hrps").
      iIntros (gid Hgid) "!> Hrp".
      iDestruct "Hrp" as "(Hvtsm & Hkvdm & Hclog & Hilog & Hbm & Hbvm & Hbtm)".
      iDestruct (big_sepS_sep_2 with "Hbvm Hbtm") as "Hrps".
      iDestruct (big_sepS_sep_2 with "Hbm Hrps") as "Hrps".
      iDestruct (big_sepS_sep_2 with "Hilog Hrps") as "Hrps".
      iDestruct (big_sepS_sep_2 with "Hclog Hrps") as "Hrps".
      iDestruct (big_sepS_sep_2 with "Hkvdm Hrps") as "Hrps".
      iDestruct (big_sepS_sep_2 with "Hvtsm Hrps") as "Hrps".
      iApply (big_sepS_impl with "Hrps").
      iIntros (rid Hrid) "!> (Hvtsm & Hkvdm & Hclog & Hilog & Hbm & Hbvm & Hbtm)".
      iFrame.
      (* Instantiate commit map, currently prepare map, key validation map, last
      accepted index map, history map, participant group map, smallest
      preparable timestamp map, prepare timestamp map. *)
      set kvdm := gset_to_gmap [false] keys_all.
      set histm := gset_to_gmap [(None : dbval)] keys_all.
      set ptsgm := gset_to_gmap O keys_all.
      set sptsgm := gset_to_gmap 1%nat keys_all.
      iExists ∅, ∅, kvdm, ∅, histm, ∅, sptsgm, ptsgm.
      iSplitL "Hkvdm".
      { iApply (big_sepS_sepM_impl with "Hkvdm").
        { by rewrite dom_gset_to_gmap. }
        iIntros (k l Hl) "!> Hl".
        by apply lookup_gset_to_gmap_Some in Hl as [_ <-].
      }
      rewrite !big_sepM_empty big_sepS_empty.
      iSplit; first done.
      iSplit.
      { iPureIntro.
        rewrite /confined_by_ballot_map.
        do 2 (split; first done).
        split; apply map_Forall2_empty.
      }
      do 2 (iSplit; first done).
      iSplit.
      { iIntros (k t).
        destruct (kvdm !! k) as [l |] eqn:Hl; rewrite Hl; last done.
        destruct (histm !! k) as [h |] eqn:Hh; rewrite Hh; last done.
        destruct (ptsgm !! k) as [n |] eqn:Hn; rewrite Hn; last done.
        destruct (l !! t) as [b |] eqn:Hb; last done.
        destruct b; last done.
        case_decide as Ht; last done.
        exfalso.
        destruct Ht as [Hth _].
        apply lookup_gset_to_gmap_Some in Hl as [_ <-].
        apply lookup_gset_to_gmap_Some in Hh as [_ <-].
        apply list_lookup_singleton_Some in Hb as [-> _].
        clear -Hth. simpl in Hth. lia.
      }
      iSplit.
      { iApply (big_sepS_elem_of with "Hloglbs"); first apply Hgid. }
      iPureIntro.
      split.
      { by rewrite /execute_cmds merge_clog_ilog_nil. }
      split; first done.
      split; first apply dom_gset_to_gmap.
      split.
      { rewrite map_Forall2_forall.
        split; last by rewrite 2!dom_gset_to_gmap.
        intros k l n Hl Hn.
        apply lookup_gset_to_gmap_Some in Hl as [_ <-].
        by apply lookup_gset_to_gmap_Some in Hn as [_ <-].
      }
      split.
      { rewrite map_Forall2_forall.
        split; last by rewrite 2!dom_gset_to_gmap.
        intros k x y Hx Hy Hnz.
        apply lookup_gset_to_gmap_Some in Hx as [_ <-].
        by apply lookup_gset_to_gmap_Some in Hy as [_ <-].
      }
      do 2 (split; first done).
      apply map_Forall2_empty.
    }
    by iFrame.
  Qed.

End alloc.
