From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.distx Require Import base res.
From Perennial.program_proof.rsm.pure Require Import dual_lookup vslice.

(** Global transaction-system invariant. *)

Definition conflict_free (future : list action) (tmodcs : gmap nat dbmap) : Prop.
Admitted.

Definition conflict_past (past future : list action) (tmodas : gmap nat dbmap) : Prop.
Admitted.

Lemma conflict_free_inv_commit_committed ts wrs future tmodcs :
  tmodcs !! ts = None ->
  head future = Some (ActCmt ts wrs) ->
  conflict_free future tmodcs ->
  conflict_free (tail future) tmodcs.
Admitted.

Lemma conflict_free_inv_commit ts wrs future tmodcs :
  head future = Some (ActCmt ts wrs) ->
  conflict_free future tmodcs ->
  conflict_free (tail future) (delete ts tmodcs).
Admitted.

Lemma conflict_past_inv_commit ts wrs past future tmodas :
  head future = Some (ActCmt ts wrs) ->
  conflict_past past future tmodas ->
  conflict_past past (tail future) tmodas.
Admitted.

Definition prophesied_or_committed (tid : nat) (wcmts wabts cmts : gset nat) :=
  (tid ∈ cmts ∧ tid ∉ wcmts) ∨
  (tid ∈ wabts ∧ tid ∉ cmts) ∨
  (tid ∈ wcmts ∧ tid ∉ cmts).

Definition res_to_tmod (res : txnres) :=
  match res with
  | ResCommitted wrs => Some wrs
  | ResAborted => None
  end.

Definition resm_to_tmods (resm : gmap nat txnres) :=
  omap res_to_tmod resm.

Definition lnrz_txns_destined
  (tids : gset nat) (tmodcs tmodas : gmap nat dbmap) (resm : gmap nat txnres) :=
  set_Forall
    (λ tid, prophesied_or_committed tid (dom tmodcs) (dom tmodas) (dom (resm_to_tmods resm)))
    tids.

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

  Definition valid_res γ ts res : iProp Σ :=
    match res with
    | ResCommitted wrs => all_prepared γ ts wrs
    | ResAborted => some_aborted γ ts
    end.

  #[global]
  Instance valid_res_persistent γ ts res :
    Persistent (valid_res γ ts res).
  Proof. destruct res; apply _. Qed.

  Definition txn_inv γ : iProp Σ :=
    ∃ (ts : nat) (tids : gset nat) (future past : list action)
      (tmodcs tmodas : gmap nat dbmap)
      (resm : gmap nat txnres) (wrsm : gmap nat dbmap),
      (* global timestamp *)
      "Hts"    ∷ ts_auth γ ts ∗
      (* linearized txns *)
      "Htxnsl" ∷ txns_lnrz_auth γ tids ∗
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
      "#Hvr"  ∷ ([∗ map] tid ↦ res ∈ resm, valid_res γ tid res) ∗
      "%Hdest" ∷ ⌜lnrz_txns_destined tids tmodcs tmodas resm⌝ ∗
      "%Hcf"   ∷ ⌜conflict_free future tmodcs⌝ ∗
      "%Hcp"   ∷ ⌜conflict_past past future tmodas⌝.

  Definition txn_inv_no_future γ future : iProp Σ :=
    ∃ (ts : nat) (tids : gset nat) (past : list action)
      (tmodcs tmodas : gmap nat dbmap)
      (resm : gmap nat txnres) (wrsm : gmap nat dbmap),
      (* global timestamp *)
      "Hts"    ∷ ts_auth γ ts ∗
      (* linearized txns *)
      "Htxnsl" ∷ txns_lnrz_auth γ tids ∗
      (* transaction result map *)
      "Hresm" ∷ txnres_auth γ resm ∗
      (* transaction write set map *)
      "Hwrsm" ∷ txnwrs_auth γ wrsm ∗
      (* key modifications *)
      "Hkmodls" ∷ ([∗ set] key ∈ keys_all, kmod_lnrz_half γ key (vslice tmodcs key)) ∗
      "Hkmodcs" ∷ ([∗ set] key ∈ keys_all, kmod_cmtd_half γ key (vslice (resm_to_tmods resm) key)) ∗
      (* safe commit/abort invariant *)
      "#Hvr"  ∷ ([∗ map] tid ↦ res ∈ resm, valid_res γ tid res) ∗
      "%Hdest" ∷ ⌜lnrz_txns_destined tids tmodcs tmodas resm⌝ ∗
      "%Hcf"   ∷ ⌜conflict_free future tmodcs⌝ ∗
      "%Hcp"   ∷ ⌜conflict_past past future tmodas⌝.

  Lemma txn_inv_extract_future γ :
    txn_inv γ -∗
    ∃ future, txn_proph γ future ∗ txn_inv_no_future γ future.
  Proof. iIntros "Htxn". iNamed "Htxn". iFrame "∗ # %". Qed.

End inv.
