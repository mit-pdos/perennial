From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.distx Require Import action base res.
From Perennial.program_proof.rsm.pure Require Import dual_lookup vslice nat.

(** Global transaction-system invariant. *)

Definition conflict_free (future : list action) (tmodcs : gmap nat dbmap) :=
  map_Forall (λ t m, first_commit_compatible future t m) tmodcs.

Definition conflict_cases
  (past future : list action) (ts : nat) (form : tcform) :=
  match form with
  | NC => no_commit future ts
  | FCI wrs => first_commit_incompatible past future ts wrs
  | FCC wrs => first_commit_compatible future ts wrs
  end.

Definition conflict_past (past future : list action) (tmodas : gmap nat tcform) :=
  map_Forall (λ t m, conflict_cases past future t m) tmodas.

Definition res_to_tmod (res : txnres) :=
  match res with
  | ResCommitted wrs => Some wrs
  | ResAborted => None
  end.

Definition resm_to_tmods (resm : gmap nat txnres) :=
  omap res_to_tmod resm.

Definition cmtxn_in_past (past : list action) (resm : gmap nat txnres) :=
  map_Forall (λ t m, ActCommit t m ∈ past) (resm_to_tmods resm).

Lemma resm_to_tmods_insert_aborted resm ts :
  resm !! ts = None ->
  resm_to_tmods (<[ts := ResAborted]> resm) = resm_to_tmods resm.
Proof.
  intros Hresm.
  apply map_eq. intros tsx.
  rewrite 2!lookup_omap.
  destruct (decide (tsx = ts)) as [-> | Hne]; last by rewrite lookup_insert_ne.
  by rewrite lookup_insert Hresm.
Qed.

Lemma resm_to_tmods_insert_committed resm ts wrs :
  resm_to_tmods (<[ts := ResCommitted wrs]> resm) = <[ts := wrs]> (resm_to_tmods resm).
Proof.
  apply map_eq. intros tsx.
  destruct (decide (tsx = ts)) as [-> | Hne]; last first.
  { rewrite lookup_insert_ne; last done.
    by rewrite 2!lookup_omap lookup_insert_ne; last done.
  }
  rewrite lookup_insert.
  by rewrite lookup_omap lookup_insert.
Qed.

Lemma vslice_resm_to_tmods_committed_absent resm ts wrs key :
  resm !! ts = Some (ResCommitted wrs) ->
  wrs !! key = None ->
  vslice (resm_to_tmods resm) key !! ts = None.
Proof.
  intros Hresm Hwrs.
  set tmods := (resm_to_tmods _).
  assert (Htmods : tmods !! ts = Some wrs).
  { rewrite lookup_omap_Some. by exists (ResCommitted wrs). }
  by rewrite lookup_vslice /dual_lookup Htmods.
Qed.

Lemma vslice_resm_to_tmods_committed_present resm ts wrs key value :
  resm !! ts = Some (ResCommitted wrs) ->
  wrs !! key = Some value ->
  vslice (resm_to_tmods resm) key !! ts = Some value.
Proof.
  intros Hresm Hwrs.
  set tmods := (resm_to_tmods _).
  assert (Htmods : tmods !! ts = Some wrs).
  { rewrite lookup_omap_Some. by exists (ResCommitted wrs). }
  by rewrite lookup_vslice /dual_lookup Htmods.
Qed.

Lemma vslice_resm_to_tmods_aborted resm ts key :
  resm !! ts = Some ResAborted ->
  vslice (resm_to_tmods resm) key !! ts = None.
Proof.
  intros Hresm.
  set tmods := (resm_to_tmods _).
  assert (Htmods : tmods !! ts = None).
  { by rewrite lookup_omap Hresm /=. }
  by rewrite lookup_vslice /dual_lookup Htmods.
Qed.

Lemma vslice_resm_to_tmods_not_terminated resm ts key :
  resm !! ts = None ->
  vslice (resm_to_tmods resm) key !! ts = None.
Proof.
  intros Hresm.
  set tmods := (resm_to_tmods _).
  assert (Htmods : tmods !! ts = None).
  { by rewrite lookup_omap Hresm /=. }
  by rewrite lookup_vslice /dual_lookup Htmods.
Qed.

Section inv.
  Context `{!distx_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : distx_names).

  Definition partitioned_tids
    γ (tids : gset nat) (tmodcs : gmap nat dbmap) (tmodas : gmap nat tcform)
    (resm : gmap nat txnres) : iProp Σ :=
    let wcmts := dom tmodcs in
    let wabts := dom tmodas in
    let cmts := dom (resm_to_tmods resm) in
    "Hwcmts" ∷ ([∗ set] tid ∈ wcmts, tids_excl_frag γ tid) ∗
    "Hwabts" ∷ ([∗ set] tid ∈ wabts, tids_excl_frag γ tid) ∗
    "Hcmts"  ∷ ([∗ set] tid ∈ cmts, tids_excl_frag γ tid) ∗
    "%Hfate" ∷ ⌜set_Forall (λ tid, tid ∈ cmts ∨ tid ∈ wabts ∨ tid ∈ wcmts) tids⌝.

  Definition past_action_witness γ (a : action) : iProp Σ :=
    match a with
    | ActCommit ts wrs => [∗ set] key ∈ dom wrs, hist_cmtd_length_lb γ key (S ts)
    | ActRead ts key => hist_cmtd_length_lb γ key ts
    end.

  #[global]
  Instance past_action_witness_persistent γ a :
    Persistent (past_action_witness γ a).
  Proof. destruct a; apply _. Qed.

  Definition all_prepared γ ts wrs : iProp Σ :=
    txnwrs_receipt γ ts wrs ∗
    [∗ set] gid ∈ ptgroups (dom wrs), txnprep_prep γ gid ts.

  Definition some_aborted γ ts : iProp Σ :=
    ∃ gid wrs, txnprep_unprep γ gid ts ∗
               txnwrs_receipt γ ts wrs ∗
               ⌜gid ∈ ptgroups (dom wrs)⌝.

  Lemma all_prepared_some_aborted_false γ ts wrs :
    all_prepared γ ts wrs -∗
    some_aborted γ ts -∗
    ⌜False⌝.
  Proof.
    iIntros "[Hwrs Hps] Habt".
    iDestruct "Habt" as (gid wrsa) "(Hnp & Hwrsa & %Hgid)".
    iDestruct (txnwrs_receipt_agree with "Hwrs Hwrsa") as %->.
    iDestruct (big_sepS_elem_of with "Hps") as "Hp"; first apply Hgid.
    by iDestruct (txnprep_receipt_agree with "Hp Hnp") as %Hcontra.
  Qed.

  Definition correct_wrs γ ts wrs : iProp Σ :=
    ∃ Q, txnpost_receipt γ ts Q ∗ ⌜Q wrs⌝.

  Definition incorrect_wrs γ ts wrs : iProp Σ :=
    ∃ Q, txnpost_receipt γ ts Q ∗ ⌜not (Q wrs)⌝.

  Definition incorrect_fcc γ ts form : iProp Σ :=
    match form with
    | FCC wrs => incorrect_wrs γ ts wrs
    |_ => True
    end.

  #[global]
  Instance incorrect_fcc_persistent γ ts form :
    Persistent (incorrect_fcc γ ts form).
  Proof. destruct form; apply _. Qed.

  Lemma correct_incorrect_wrs γ ts wrs :
    correct_wrs γ ts wrs -∗
    incorrect_wrs γ ts wrs -∗
    False.
  Proof.
    iIntros "(%pos & Hpos & %Hpos) (%neg & Hneg & %Hneg)".
    iDestruct (txnpost_receipt_agree with "Hpos Hneg") as %->.
    done.
  Qed.

  Definition valid_res γ ts res : iProp Σ :=
    match res with
    | ResCommitted wrs => all_prepared γ ts wrs
    | ResAborted => some_aborted γ ts
    end.

  #[global]
  Instance valid_res_persistent γ ts res :
    Persistent (valid_res γ ts res).
  Proof. destruct res; apply _. Qed.

  Definition txnsys_inv γ : iProp Σ :=
    ∃ (ts : nat) (tids : gset nat) (future past : list action)
      (tmodcs : gmap nat dbmap) (tmodas : gmap nat tcform) (posts : gmap nat (dbmap -> Prop))
      (resm : gmap nat txnres) (wrsm : gmap nat dbmap),
      (* global timestamp *)
      "Hts"    ∷ ts_auth γ ts ∗
      (* witnesses of txn linearization *)
      "Htxnsl" ∷ txns_lnrz_auth γ tids ∗
      (* exclusive transaction IDs *)
      "Hexcl" ∷ tids_excl_auth γ tids ∗
      "Hpart" ∷ partitioned_tids γ tids tmodcs tmodas resm ∗
      (* transaction post-conditions; a better design seems to be moving this out of [txnsys_inv] *)
      "Hpost" ∷ txnpost_auth γ posts ∗
      (* prophecy variable *)
      "Hproph" ∷ txn_proph γ future ∗
      (* transaction result map *)
      "Hresm" ∷ txnres_auth γ resm ∗
      (* transaction write set map *)
      "Hwrsm" ∷ txnwrs_auth γ wrsm ∗
      (* key modifications *)
      "Hkmodls" ∷ ([∗ set] key ∈ keys_all, kmod_lnrz_half γ key (vslice tmodcs key)) ∗
      "Hkmodcs" ∷ ([∗ set] key ∈ keys_all, kmod_cmtd_half γ key (vslice (resm_to_tmods resm) key)) ∗
      (* safe commit/abort invariant *)
      "#Hvr" ∷ ([∗ map] tid ↦ res ∈ resm, valid_res γ tid res) ∗
      (* post-conditions hold on the write-set map *)
      "#Hcwrs" ∷ ([∗ map] tid ↦ wrs ∈ wrsm, correct_wrs γ tid wrs) ∗
      (* post-conditions not hold on the write set for the FCC case *)
      "#Hiwrs" ∷ ([∗ map] tid ↦ form ∈ tmodas, incorrect_fcc γ tid form) ∗
      (* past action witnesses *)
      "#Hpas" ∷ ([∗ list] a ∈ past, past_action_witness γ a) ∗
      "%Htsge" ∷ ⌜ge_all ts tids⌝ ∗
      "%Hdomq" ∷ ⌜dom posts = tids⌝ ∗
      "%Hcmtxn" ∷ ⌜cmtxn_in_past past resm⌝ ∗
      "%Hwrsm"  ∷ ⌜map_Forall (λ tid wrs, valid_ts tid ∧ valid_wrs wrs) wrsm⌝ ∗
      "%Hnz"    ∷ ⌜nz_all (dom tmodcs)⌝ ∗
      "%Hcf"    ∷ ⌜conflict_free future tmodcs⌝ ∗
      "%Hcp"    ∷ ⌜conflict_past past future tmodas⌝.

  Definition txnsys_inv_no_future γ future : iProp Σ :=
    ∃ (ts : nat) (tids : gset nat) (past : list action)
      (tmodcs : gmap nat dbmap) (tmodas : gmap nat tcform) (posts : gmap nat (dbmap -> Prop))
      (resm : gmap nat txnres) (wrsm : gmap nat dbmap),
      (* global timestamp *)
      "Hts"    ∷ ts_auth γ ts ∗
      (* witnesses of txn linearization *)
      "Htxnsl" ∷ txns_lnrz_auth γ tids ∗
      (* exclusive transaction IDs *)
      "Hexcl" ∷ tids_excl_auth γ tids ∗
      "Hpart" ∷ partitioned_tids γ tids tmodcs tmodas resm ∗
      (* transaction post-conditions *)
      "Hpost" ∷ txnpost_auth γ posts ∗
      (* transaction result map *)
      "Hresm" ∷ txnres_auth γ resm ∗
      (* transaction write set map *)
      "Hwrsm" ∷ txnwrs_auth γ wrsm ∗
      (* key modifications *)
      "Hkmodls" ∷ ([∗ set] key ∈ keys_all, kmod_lnrz_half γ key (vslice tmodcs key)) ∗
      "Hkmodcs" ∷ ([∗ set] key ∈ keys_all, kmod_cmtd_half γ key (vslice (resm_to_tmods resm) key)) ∗
      (* safe commit/abort invariant *)
      "#Hvr" ∷ ([∗ map] tid ↦ res ∈ resm, valid_res γ tid res) ∗
      (* post-conditions hold on the write-set map *)
      "#Hcwrs" ∷ ([∗ map] tid ↦ wrs ∈ wrsm, correct_wrs γ tid wrs) ∗
      (* post-conditions not hold on the write set for the FCC case *)
      "#Hiwrs" ∷ ([∗ map] tid ↦ form ∈ tmodas, incorrect_fcc γ tid form) ∗
      (* past action witnesses *)
      "#Hpas" ∷ ([∗ list] a ∈ past, past_action_witness γ a) ∗
      "%Htsge" ∷ ⌜ge_all ts tids⌝ ∗
      "%Hdomq" ∷ ⌜dom posts = tids⌝ ∗
      "%Hcmtxn" ∷ ⌜cmtxn_in_past past resm⌝ ∗
      "%Hwrsm" ∷ ⌜map_Forall (λ tid wrs, valid_ts tid ∧ valid_wrs wrs) wrsm⌝ ∗
      "%Hnz"   ∷ ⌜nz_all (dom tmodcs)⌝ ∗
      "%Hcf"   ∷ ⌜conflict_free future tmodcs⌝ ∗
      "%Hcp"   ∷ ⌜conflict_past past future tmodas⌝.

  Lemma txnsys_inv_extract_future γ :
    txnsys_inv γ -∗
    ∃ future, txn_proph γ future ∗ txnsys_inv_no_future γ future.
  Proof. iIntros "Htxn". iNamed "Htxn". iFrame "∗ # %". Qed.

  Definition txnsys_inv_with_future_no_ts γ future ts : iProp Σ :=
    ∃ (tids : gset nat) (past : list action)
      (tmodcs : gmap nat dbmap) (tmodas : gmap nat tcform) (posts : gmap nat (dbmap -> Prop))
      (resm : gmap nat txnres) (wrsm : gmap nat dbmap),
      (* witnesses of txn linearization *)
      "Htxnsl" ∷ txns_lnrz_auth γ tids ∗
      (* exclusive transaction IDs *)
      "Hexcl" ∷ tids_excl_auth γ tids ∗
      "Hpart" ∷ partitioned_tids γ tids tmodcs tmodas resm ∗
      (* transaction post-conditions *)
      "Hpost" ∷ txnpost_auth γ posts ∗
      (* transaction result map *)
      "Hresm" ∷ txnres_auth γ resm ∗
      (* transaction write set map *)
      "Hwrsm" ∷ txnwrs_auth γ wrsm ∗
      (* key modifications *)
      "Hkmodls" ∷ ([∗ set] key ∈ keys_all, kmod_lnrz_half γ key (vslice tmodcs key)) ∗
      "Hkmodcs" ∷ ([∗ set] key ∈ keys_all, kmod_cmtd_half γ key (vslice (resm_to_tmods resm) key)) ∗
      (* safe commit/abort invariant *)
      "#Hvr" ∷ ([∗ map] tid ↦ res ∈ resm, valid_res γ tid res) ∗
      (* post-conditions hold on the write-set map *)
      "#Hcwrs" ∷ ([∗ map] tid ↦ wrs ∈ wrsm, correct_wrs γ tid wrs) ∗
      (* post-conditions not hold on the write set for the FCC case *)
      "#Hiwrs" ∷ ([∗ map] tid ↦ form ∈ tmodas, incorrect_fcc γ tid form) ∗
      (* past action witnesses *)
      "#Hpas" ∷ ([∗ list] a ∈ past, past_action_witness γ a) ∗
      "%Htsge" ∷ ⌜ge_all ts tids⌝ ∗
      "%Hdomq" ∷ ⌜dom posts = tids⌝ ∗
      "%Hcmtxn" ∷ ⌜cmtxn_in_past past resm⌝ ∗
      "%Hwrsm" ∷ ⌜map_Forall (λ tid wrs, valid_ts tid ∧ valid_wrs wrs) wrsm⌝ ∗
      "%Hnz"   ∷ ⌜nz_all (dom tmodcs)⌝ ∗
      "%Hcf"   ∷ ⌜conflict_free future tmodcs⌝ ∗
      "%Hcp"   ∷ ⌜conflict_past past future tmodas⌝.

  Lemma txnsys_inv_expose_future_extract_ts γ :
    txnsys_inv γ -∗
    ∃ future ts, txnsys_inv_with_future_no_ts γ future ts ∗ ts_auth γ ts.
  Proof. iIntros "Htxn". iNamed "Htxn". iFrame "∗ # %". Qed.

End inv.
