From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import list.
From Perennial.program_proof.tulip Require Import base cmd res.
(* TODO: might be better to separate out the common definitions from [inv_group]. *)
From Perennial.program_proof.tulip Require Import inv_group.

Section inv.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  Definition safe_replica_prepare γ gid ts st : iProp Σ :=
    match st with
    | StPrepared pwrs => is_txn_pwrs γ gid ts pwrs
    | _ => True
    end.

  #[global]
  Instance safe_replica_prepare_persistent γ gid ts st :
    Persistent (safe_replica_prepare γ gid ts st).
  Proof. destruct st; apply _. Defined.

  Definition validated_pwrs_of_txn γ gid rid vts : iProp Σ :=
    ∃ pwrs, is_txn_pwrs γ gid vts pwrs ∗
            ([∗ set] key ∈ dom pwrs, is_replica_key_validated_at γ gid rid key vts).

  Definition group_aborted_if_validated
    γ gid (kvdm : gmap dbkey (list bool)) (histm : gmap dbkey dbhist)
    (ptsm : gmap dbkey nat) : iProp Σ :=
    ∀ k ts,
    match kvdm !! k, histm !! k, ptsm !! k with
    | Some vdl, Some hist, Some pts =>
        match vdl !! ts with
        | Some true => if decide ((length hist ≤ ts)%nat ∧ ts ≠ pts)
                      then is_group_aborted γ gid ts
                      else True
        | _ => True
        end
    | _, _, _ => True
    end.

  Definition replica_inv_with_cm_with_stm
    γ (gid rid : u64) (cm : gmap nat bool) (stm : gmap nat txnst) : iProp Σ :=
    ∃ (clog : dblog) (vtss : gset nat) (kvdm : gmap dbkey (list bool))
      (histm : gmap dbkey dbhist) (sptsm ptsm : gmap dbkey nat),
      "Hvtss"     ∷ own_replica_validated_tss γ gid rid vtss ∗
      "Hkvdm"     ∷ ([∗ map] k ↦ vd ∈ kvdm, own_replica_key_validation γ gid rid k vd) ∗
      "Hhistm"    ∷ ([∗ map] k ↦ h ∈ histm, own_dura_hist_half γ rid k h) ∗
      "Hsptsm"    ∷ ([∗ map] k ↦ spts ∈ sptsm, own_replica_spts_half γ rid k spts) ∗
      "Hptsm"     ∷ ([∗ map] k ↦ pts ∈ ptsm, own_replica_pts_half γ rid k pts) ∗
      "#Hclog"    ∷ is_txn_log_lb γ gid clog ∗
      "#Hreplhm"  ∷ ([∗ map] k ↦ h ∈ histm, is_repl_hist_lb γ k h) ∗
      "#Hsafep"   ∷ ([∗ map] ts ↦ st ∈ stm, safe_replica_prepare γ gid ts st) ∗
      "#Hvpwrs"   ∷ ([∗ set] ts ∈ vtss, validated_pwrs_of_txn γ gid rid ts) ∗
      "#Hgabt"    ∷ group_aborted_if_validated γ gid kvdm histm ptsm ∗
      "%Hrsm"     ∷ ⌜apply_cmds clog = State cm histm⌝ ∗
      "%Hdomstm"  ∷ ⌜vtss ⊆ dom stm⌝ ∗
      "%Hdomkvdm" ∷ ⌜dom kvdm = keys_all⌝ ∗
      "%Hlenkvd"  ∷ ⌜map_Forall2 (λ _ vd spts, length vd = spts) kvdm sptsm⌝ ∗
      "%Hsptsmlk" ∷ ⌜map_Forall2 (λ _ spts pts, pts ≠ O -> spts = S pts) sptsm ptsm⌝ ∗
      "%Hcm"      ∷ ⌜cm = omap txnst_to_option_bool stm⌝ ∗
      "%Hpil"     ∷ ⌜prepared_impl_locked stm ptsm⌝.

  Definition replica_inv γ (gid rid : u64) : iProp Σ :=
    ∃ cm stm, "Hrp" ∷ replica_inv_with_cm_with_stm γ gid rid cm stm.

  Definition replica_inv_xfinalized γ (gid rid : u64) (tss : gset nat) : iProp Σ :=
    ∃ cm stm,
      "Hrp"      ∷ replica_inv_with_cm_with_stm γ gid rid cm stm ∗
      "%Hxfinal" ∷ ⌜set_Forall (λ t, cm !! t = None) tss⌝.

  Lemma replica_inv_xfinalized_empty γ gid rid :
    replica_inv γ gid rid -∗
    replica_inv_xfinalized γ gid rid ∅.
  Proof. iNamed 1. iFrame. iPureIntro. apply set_Forall_empty. Qed.

  Lemma replicas_inv_xfinalized_empty γ gid rids :
    ([∗ set] rid ∈ rids, replica_inv γ gid rid) -∗
    ([∗ set] rid ∈ rids, replica_inv_xfinalized γ gid rid ∅).
  Proof.
    iIntros "Hreplicas".
    iApply (big_sepS_mono with "Hreplicas").
    iIntros (rid Hrid).
    iApply replica_inv_xfinalized_empty.
  Qed.

  Lemma replica_inv_xfinalized_validated_impl_prepared
    γ gid rid cm stm (tss : gset nat) ts :
    set_Forall (λ t, cm !! t = None) tss ->
    ts ∈ tss ->
    is_replica_validated_ts γ gid rid ts -∗
    replica_inv_with_cm_with_stm γ gid rid cm stm -∗
    ⌜∃ pwrs, stm !! ts = Some (StPrepared pwrs)⌝.
  Proof.
    iIntros (Hxfinal Hin) "Hvd Hrp".
    iNamed "Hrp".
    iDestruct (replica_validated_ts_elem_of with "Hvd Hvtss") as %Hinvtss.
    destruct (stm !! ts) as [st |] eqn:Hstm; last first.
    { exfalso.
      rewrite -not_elem_of_dom in Hstm.
      clear -Hdomstm Hinvtss Hstm. set_solver.
    }
    specialize (Hxfinal _ Hin). simpl in Hxfinal.
    destruct st as [pwrs | |]; last first.
    { exfalso. by rewrite Hcm lookup_omap Hstm in Hxfinal. }
    { exfalso. by rewrite Hcm lookup_omap Hstm in Hxfinal. }
    by eauto.
  Qed.

  Lemma replica_inv_validated_keys_of_txn γ gid rid ts :
    is_replica_validated_ts γ gid rid ts -∗
    replica_inv γ gid rid -∗
    validated_pwrs_of_txn γ gid rid ts.
  Proof.
    iIntros "#Hvd Hrp".
    do 2 iNamed "Hrp".
    iDestruct (replica_validated_ts_elem_of with "Hvd Hvtss") as %Hinvtss.
    by iDestruct (big_sepS_elem_of with "Hvpwrs") as "Hvts"; first apply Hinvtss.
  Qed.

  Lemma replicas_inv_validated_keys_of_txn γ gid rids ts :
    ([∗ set] rid ∈ rids, is_replica_validated_ts γ gid rid ts) -∗
    ([∗ set] rid ∈ rids, replica_inv γ gid rid) -∗
    ([∗ set] rid ∈ rids, validated_pwrs_of_txn γ gid rid ts).
  Proof.
    iIntros "#Hvds Hrps".
    iApply big_sepS_forall.
    iIntros (rid Hrid).
    iDestruct (big_sepS_elem_of with "Hvds") as "Hvd"; first apply Hrid.
    iDestruct (big_sepS_elem_of with "Hrps") as "Hrp"; first apply Hrid.
    iApply (replica_inv_validated_keys_of_txn with "Hvd Hrp").
  Qed.

  Definition read_promise γ gid rid key lb ub : iProp Σ :=
    ∃ vdl,
      "#Hvdl"    ∷ is_replica_key_validation_lb γ gid rid key vdl ∗
      "#Habtifp" ∷ ([∗ list] i ↦ b ∈ vdl,
                      ⌜(lb < i)%nat ∧ b = true⌝ -∗ is_group_aborted γ gid i) ∗
      "%Hlenvdl" ∷ ⌜length vdl = ub⌝.

  Lemma read_promise_weaken_lb {γ gid rid key lb ub} lb' :
    (lb ≤ lb')%nat ->
    read_promise γ gid rid key lb ub -∗
    read_promise γ gid rid key lb' ub.
  Proof.
    iIntros (Hge).
    iNamed 1.
    iFrame "Hvdl %".
    iApply (big_sepL_impl with "Habtifp").
    iIntros (t b Hb) "!> Habt [%Ht %Htrue]".
    iApply "Habt".
    iPureIntro.
    split; [lia | done].
  Qed.

  Lemma read_promise_weaken_ub {γ gid rid key lb ub} ub' :
    (ub' ≤ ub)%nat ->
    read_promise γ gid rid key lb ub -∗
    read_promise γ gid rid key lb ub'.
  Proof.
    iIntros (Hle).
    iNamed 1.
    iDestruct (replica_key_validation_lb_weaken (take ub' vdl) with "Hvdl") as "Hvdl'".
    { apply prefix_take. }
    iFrame "Hvdl'".
    iSplit; last first.
    { iPureIntro. rewrite length_take. lia. }
    by iDestruct (big_sepL_take_drop _ _ ub' with "Habtifp") as "[Htake Hdrop]".
  Qed.

End inv.
