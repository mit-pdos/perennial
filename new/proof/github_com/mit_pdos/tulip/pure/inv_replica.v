From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import list.
From Perennial.program_proof.tulip Require Import base cmd res stability.
(* TODO: might be better to separate out the common definitions from [inv_group]. *)
From Perennial.program_proof.tulip Require Import inv_group.

Definition rank_freshness {A} (blt : ballot) (m : gmap nat A) :=
  ∀ rank, (length blt < rank)%nat -> m !! rank = None.

Definition confined_by_ballot_map {A} (bm : gmap nat ballot) (mm : gmap nat (gmap nat A)) :=
  map_Forall2 (λ _ l m, rank_freshness l m) bm mm.

(* TODO: Remove "_cpm" if we can also remove [stm] in the group invariant. *)
Definition prepared_impl_locked_cpm (cpm : gmap nat dbmap) (ptsm : gmap dbkey nat) :=
  ∀ ts pwrs key,
  cpm !! ts = Some pwrs ->
  key ∈ dom pwrs ->
  ptsm !! key = Some ts.

Lemma prepared_impl_locked_disjoint cpm ptsm t1 t2 pwrs1 pwrs2 :
  t1 ≠ t2 ->
  cpm !! t1 = Some pwrs1 ->
  cpm !! t2 = Some pwrs2 ->
  prepared_impl_locked_cpm cpm ptsm ->
  dom pwrs1 ## dom pwrs2.
Proof.
  intros Hne Hpwrs1 Hpwrs2 Hpil.
  rewrite elem_of_disjoint.
  intros Hk Hin1 Hin2.
  pose proof (Hpil _ _ _ Hpwrs1 Hin1) as Ht1.
  pose proof (Hpil _ _ _ Hpwrs2 Hin2) as Ht2.
  rewrite Ht1 in Ht2.
  inv Ht2.
Qed.

Section inv.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

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

  Definition safe_ballot γ gid ts (l : ballot) : iProp Σ :=
    ∀ r,
    if decide (r = O)
    then True
    else match l !! r with
         | Some (Accept p) => is_group_prepare_proposal γ gid ts r p
         | _ => True
         end.

  Definition replica_inv_ballot_map γ gid rid bm : iProp Σ :=
    "Hblt"      ∷ own_replica_ballot_map γ gid rid bm ∗
    "#Hsafebm"  ∷ ([∗ map] ts ↦ l ∈ bm, safe_ballot γ gid ts l).

  Definition replica_inv_backup γ gid rid (bm : gmap nat ballot) : iProp Σ :=
    ∃ (bvm : gmap nat (gmap nat coordid)) (btm : gmap nat (gmap nat (gset u64))),
      "Hbvm"     ∷ own_replica_backup_vote_map γ gid rid bvm ∗
      "Hbtm"     ∷ own_replica_backup_tokens_map γ gid rid btm ∗
      "%Hdombvm" ∷ ⌜dom bvm = dom bm⌝ ∗
      "%Hdombtm" ∷ ⌜dom btm = dom bm⌝ ∗
      "%Hbmbvm"  ∷ ⌜confined_by_ballot_map bm bvm⌝ ∗
      "%Hbmbtm"  ∷ ⌜confined_by_ballot_map bm btm⌝.

  Definition fast_proposal_witness γ gid rid ts (ps : nat * bool) : iProp Σ :=
    (if decide (ps.1 = O)
     then is_replica_pdec_at_rank γ gid rid ts O ps.2 ∗
          if ps.2 then is_replica_validated_ts γ gid rid ts else True
     else True)%I.

  #[global]
  Instance fast_proposal_witness_persistent γ gid rid ts ps :
    Persistent (fast_proposal_witness γ gid rid ts ps).
  Proof. rewrite /fast_proposal_witness. apply _. Defined.

  Definition eq_lsn_last_ilog (lsna : nat) (ilog : list (nat * icommand)) :=
    match last ilog with
    | Some (n, _) => n = lsna
    | _ => lsna = O
    end.

  Definition ge_lsn_last_ilog (lsna : nat) (ilog : list (nat * icommand)) :=
    match last ilog with
    | Some (n, _) => (n ≤ lsna)%nat
    | _ => True
    end.

  Lemma eq_lsn_last_ilog_weaken n ilog :
    eq_lsn_last_ilog n ilog ->
    ge_lsn_last_ilog n ilog.
  Proof.
    rewrite /eq_lsn_last_ilog /ge_lsn_last_ilog.
    intros Hlsn.
    destruct (last ilog) as [[n' c] |]; [lia | done].
  Qed.

  Lemma ge_lsn_last_ilog_weaken n1 n2 ilog :
    (n1 ≤ n2)%nat ->
    ge_lsn_last_ilog n1 ilog ->
    ge_lsn_last_ilog n2 ilog.
  Proof.
    rewrite /ge_lsn_last_ilog.
    intros Hle Hlsn.
    destruct (last ilog) as [[n c] |]; [lia | done].
  Qed.

  Definition ilog_lsn_sorted (ilog : list (nat * icommand)) :=
    ∀ i j x y, (i ≤ j)%nat -> ilog !! i = Some x -> ilog !! j = Some y -> (x.1 ≤ y.1)%nat.

  Lemma ilog_lsn_sorted_inv_snoc (lsn : nat) (icmd : icommand) ilog :
    ge_lsn_last_ilog lsn ilog ->
    ilog_lsn_sorted ilog ->
    ilog_lsn_sorted (ilog ++ [(lsn, icmd)]).
  Proof.
    intros Hge Hsorted i j x y Hij Hx Hy.
    destruct (decide (j = length ilog)) as [Heqj | Hne]; last first.
    { (* Case: [j] points to an old entry. *)
      apply lookup_lt_Some in Hy as Hj.
      rewrite length_app /= in Hj.
      rewrite lookup_app_l in Hx; last first.
      { clear -Hij Hne Hj. lia. }
      rewrite lookup_app_l in Hy; last first.
      { clear -Hne Hj. lia. }
      by specialize (Hsorted _ _ _ _ Hij Hx Hy).
    }
    (* Case: [j] points to the new entry. *)
    destruct (decide (i = length ilog)) as [Heqi | Hne].
    { (* Case: [i] points to the new entry. *)
      subst i j. rewrite Hx in Hy. by inv Hy.
    }
    (* Case: [i] points to an old entry. *)
    subst j. rewrite lookup_snoc_length in Hy. inv Hy. simpl.
    apply lookup_lt_Some in Hx as Hi.
    rewrite length_app /= in Hi.
    assert (Hlt : (i < length ilog)%nat).
    { clear -Hne Hi. lia. }
    rewrite lookup_app_l in Hx; last apply Hlt.
    rewrite /ge_lsn_last_ilog in Hge.
    destruct (last ilog) as [[n c] |] eqn:Hlast; last first.
    { rewrite last_None in Hlast. rewrite Hlast /= in Hlt.
      clear -Hlt. lia.
    }
    rewrite last_lookup in Hlast.
    trans n; last apply Hge.
    unshelve epose proof (Hsorted _ _ _ _ _ Hx Hlast) as Hle.
    { clear -Hlt. lia. }
    apply Hle.
  Qed.

  Definition replica_inv_internal
    γ (gid rid : u64) (clog : dblog) (ilog : list (nat * icommand))
    (cm : gmap nat bool) (cpm : gmap nat dbmap) (weak : bool) : iProp Σ :=
    ∃ (vtss : gset nat) (kvdm : gmap dbkey (list bool)) (bm : gmap nat ballot)
      (histm : gmap dbkey dbhist) (ptgsm : gmap nat (gset u64)) (sptsm ptsm : gmap dbkey nat)
      (psm : gmap nat (nat * bool)) (rkm : gmap nat nat),
      let log := merge_clog_ilog clog ilog in
      let lenc := length clog in
      "Hvtss"     ∷ own_replica_validated_tss γ gid rid vtss ∗
      "Hclog"     ∷ own_replica_clog_half γ gid rid clog ∗
      "Hilog"     ∷ own_replica_ilog_half γ gid rid ilog ∗
      "Hkvdm"     ∷ ([∗ map] k ↦ vd ∈ kvdm, own_replica_key_validation γ gid rid k vd) ∗
      "Hbm"       ∷ replica_inv_ballot_map γ gid rid bm ∗
      "Hbackup"   ∷ replica_inv_backup γ gid rid bm ∗
      "#Hsafep"   ∷ ([∗ map] ts ↦ pwrs ∈ cpm, safe_txn_pwrs γ gid ts pwrs) ∗
      "#Hrpvds"   ∷ ([∗ set] t ∈ dom cpm, is_replica_validated_ts γ gid rid t) ∗
      "#Hfpw"     ∷ ([∗ map] t ↦ ps ∈ psm, fast_proposal_witness γ gid rid t ps) ∗
      "#Hlnrzs"   ∷ ([∗ set] t ∈ dom ptgsm, is_lnrz_tid γ t) ∗
      "#Hsafebk"  ∷ ([∗ map] t ↦ g ∈ ptgsm, safe_backup_txn γ t g) ∗
      "#Hvpwrs"   ∷ ([∗ set] ts ∈ vtss, validated_pwrs_of_txn γ gid rid ts) ∗
      "#Hgabt"    ∷ group_aborted_if_validated γ gid kvdm histm ptsm ∗
      "#Hcloglb"  ∷ is_txn_log_lb γ gid clog ∗
      "%Heqlast"  ∷ ⌜(if weak then ge_lsn_last_ilog lenc ilog else eq_lsn_last_ilog lenc ilog)⌝ ∗
      "%Hisorted" ∷ ⌜ilog_lsn_sorted ilog⌝ ∗
      "%Hrsm"     ∷ ⌜execute_cmds log = LocalState cm histm cpm ptgsm sptsm ptsm psm rkm⌝ ∗
      "%Hcloglen" ∷ ⌜Forall (λ nc, (nc.1 <= length clog)%nat) ilog⌝ ∗
      "%Hvtss"    ∷ ⌜vtss ⊆ dom cm ∪ dom cpm⌝ ∗
      "%Hdomkvdm" ∷ ⌜dom kvdm = keys_all⌝ ∗
      "%Hlenkvd"  ∷ ⌜map_Forall2 (λ _ vd spts, length vd = S spts) kvdm sptsm⌝ ∗
      "%Hsptsmlk" ∷ ⌜map_Forall2 (λ _ spts pts, pts ≠ O -> spts = pts) sptsm ptsm⌝ ∗
      "%Hpil"     ∷ ⌜prepared_impl_locked_cpm cpm ptsm⌝ ∗
      "%Hcpmnz"   ∷ ⌜cpm !! O = None⌝ ∗
      "%Hbmpsm"   ∷ ⌜map_Forall2 (λ _ l p, latest_term l = p.1 ∧ l !! p.1 = Some (Accept p.2)) bm psm⌝ ∗
      "%Hbmrkm"   ∷ ⌜map_Forall2 (λ _ l r, length l = r) bm rkm⌝.

  Definition replica_inv_with_cm_with_cpm
    γ (gid rid : u64) (cm : gmap nat bool) (cpm : gmap nat dbmap) : iProp Σ :=
    ∃ clog ilog, "Hrp" ∷ replica_inv_internal γ gid rid clog ilog cm cpm false.

  Definition replica_inv γ (gid rid : u64) : iProp Σ :=
    ∃ clog ilog cm cpm, "Hrp" ∷ replica_inv_internal γ gid rid clog ilog cm cpm false.

  Definition replica_inv_weak γ (gid rid : u64) : iProp Σ :=
    ∃ clog ilog cm cpm, "Hrp" ∷ replica_inv_internal γ gid rid clog ilog cm cpm true.

  #[global]
  Instance replica_inv_timeless γ gid rid :
    Timeless (replica_inv γ gid rid).
  Proof.
    rewrite /replica_inv.
    repeat (apply exist_timeless => ?).
    repeat (apply sep_timeless; try apply _).
    apply big_sepM_timeless. intros ???.
    rewrite /fast_proposal_witness.
    apply _.
  Qed.

  Lemma replica_inv_weaken γ gid rid :
    replica_inv γ gid rid -∗
    replica_inv_weak γ gid rid.
  Proof.
    iIntros "Hrp".
    do 2 iNamed "Hrp".
    iFrame "∗ # %".
    iPureIntro.
    by apply eq_lsn_last_ilog_weaken.
  Qed.

  Definition replica_inv_xfinalized γ (gid rid : u64) (ptsm : gset nat) : iProp Σ :=
    ∃ cm cpm,
      "Hrp"      ∷ replica_inv_with_cm_with_cpm γ gid rid cm cpm ∗
      "%Hxfinal" ∷ ⌜set_Forall (λ t, cm !! t = None) ptsm⌝.

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
    γ gid rid cm cpm (tss : gset nat) ts :
    set_Forall (λ t, cm !! t = None) tss ->
    ts ∈ tss ->
    is_replica_validated_ts γ gid rid ts -∗
    replica_inv_with_cm_with_cpm γ gid rid cm cpm -∗
    ⌜∃ pwrs, cpm !! ts = Some pwrs⌝.
  Proof.
    iIntros (Hxfinal Hin) "Hvd Hrp".
    do 2 iNamed "Hrp".
    iDestruct (replica_validated_ts_elem_of with "Hvd Hvtss") as %Hinvtss.
    destruct (cpm !! ts) as [pwrs |] eqn:Hpwrs; first by eauto.
    exfalso.
    specialize (Hxfinal _ Hin).
    apply not_elem_of_dom in Hpwrs, Hxfinal.
    clear -Hpwrs Hxfinal Hvtss Hinvtss.
    set_solver.
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

  Definition prepare_promise γ gid rid (ts : nat) (rk rkl : nat) (p : bool) : iProp Σ :=
    ∃ lb : ballot,
      "#Hlb"    ∷ is_replica_ballot_lb γ gid rid ts lb ∗
      "#Hgpsl"  ∷ is_group_prepare_proposal_if_classic γ gid ts rkl p ∗
      "%Hp"     ∷ ⌜lb !! rkl = Some (Accept p)⌝ ∗
      "%Hlenlb" ∷ ⌜length lb = rk⌝ ∗
      "%Hrkl"   ∷ ⌜rkl = latest_term lb⌝.

  Lemma replica_inv_weaken_ballot_map γ gid rid :
    replica_inv γ gid rid -∗
    ∃ bm, replica_inv_ballot_map γ gid rid bm.
  Proof. iIntros "Hrp". do 2 iNamed "Hrp". iFrame "Hbm". Qed.

  Lemma replicas_inv_weaken_ballot_map γ gid rids :
    ([∗ set] rid ∈ rids, replica_inv γ gid rid) -∗
    ∃ bmm,
      ([∗ map] rid ↦ bm ∈ bmm, replica_inv_ballot_map γ gid rid bm) ∗
      ⌜dom bmm = rids⌝.
  Proof.
    iIntros "Hrps".
    iDestruct (big_sepS_impl with "Hrps []") as "Hrps".
    { iIntros (rid Hrid) "!> Hrp".
      iApply (replica_inv_weaken_ballot_map with "Hrp").
    }
    iDestruct (big_sepS_exists_sepM with "Hrps") as (bmm) "[%Hdom Hrps]".
    iFrame "Hrps %".
  Qed.

End inv.
