From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.distx Require Import base res.
From Perennial.program_proof.rsm.pure Require Import dual_lookup.

(** Global transaction-system invariant. *)

Definition conflict_free (acts : list action) (txns : gmap nat dbmap) : Prop.
Admitted.

Definition conflict_past (acts_future acts_past : list action) (txns : gmap nat dbmap) : Prop.
Admitted.

Definition cmtd_impl_prep (resm : gmap nat txnres) (wrsm : gmap nat dbmap) :=
  ∀ ts, match resm !! ts with
        | Some (ResCommitted wrs) => wrsm !! ts = Some wrs
        | _ => True
        end.

Definition tmods_kmods_consistent (tmods : gmap nat dbmap) (kmods : gmap dbkey dbkmod) :=
  dual_lookup_consistent tmods kmods.

Definition res_to_tmod (res : txnres) :=
  match res with
  | ResCommitted wrs => Some wrs
  | ResAborted => None
  end.

Definition resm_to_tmods (resm : gmap nat txnres) :=
  omap res_to_tmod resm.

Lemma resm_cmted_kmod_absent resm kmods kmod ts wrs key :
  resm !! ts = Some (ResCommitted wrs) ->
  wrs !! key = None ->
  kmods !! key = Some kmod ->
  tmods_kmods_consistent (resm_to_tmods resm) kmods ->
  kmod !! ts = None.
Proof.
  intros Hresm Hwrs Hkmods Hc.
  set tmods := (resm_to_tmods _) in Hc.
  assert (Htmods : tmods !! ts = Some wrs).
  { rewrite lookup_omap_Some. by exists (ResCommitted wrs). }
  specialize (Hc ts key).
  by rewrite /dual_lookup Htmods Hkmods Hwrs in Hc.
Qed.

Lemma resm_cmted_kmod_present resm kmods kmod ts wrs key value :
  resm !! ts = Some (ResCommitted wrs) ->
  wrs !! key = Some value ->
  kmods !! key = Some kmod ->
  tmods_kmods_consistent (resm_to_tmods resm) kmods ->
  kmod !! ts = Some value.
Proof.
  intros Hresm Hwrs Hkmods Hc.
  set tmods := (resm_to_tmods _) in Hc.
  assert (Htmods : tmods !! ts = Some wrs).
  { rewrite lookup_omap_Some. by exists (ResCommitted wrs). }
  specialize (Hc ts key).
  by rewrite /dual_lookup Htmods Hkmods Hwrs in Hc.
Qed.

Lemma resm_abted_kmod_absent resm kmods kmod ts key :
  resm !! ts = Some ResAborted ->
  kmods !! key = Some kmod ->
  tmods_kmods_consistent (resm_to_tmods resm) kmods ->
  kmod !! ts = None.
Proof.
  intros Hresm Hkmods Hc.
  set tmods := (resm_to_tmods _) in Hc.
  assert (Htmods : tmods !! ts = None).
  { by rewrite lookup_omap Hresm /=. }
  specialize (Hc ts key).
  by rewrite /dual_lookup Htmods Hkmods in Hc.
Qed.

Lemma resm_absent_kmod_absent resm kmods kmod ts key :
  resm !! ts = None ->
  kmods !! key = Some kmod ->
  tmods_kmods_consistent (resm_to_tmods resm) kmods ->
  kmod !! ts = None.
Proof.
  intros Hresm Hkmods Hc.
  set tmods := (resm_to_tmods _) in Hc.
  assert (Htmods : tmods !! ts = None).
  { by rewrite lookup_omap Hresm /=. }
  specialize (Hc ts key).
  by rewrite /dual_lookup Htmods Hkmods in Hc.
Qed.

Section inv.
  Context `{!distx_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : distx_names).

  Definition all_prepared γ ts keys : iProp Σ :=
    [∗ set] gid ∈ ptgroups keys, txnprep_prep γ gid ts.

  Definition some_aborted γ ts : iProp Σ :=
    ∃ gid, txnprep_unprep γ gid ts.

  Definition valid_res γ ts res : iProp Σ :=
    match res with
    | ResCommitted wrs => all_prepared γ ts (dom wrs)
    | ResAborted => some_aborted γ ts
    end.

  #[global]
  Instance valid_res_persistent γ ts res :
    Persistent (valid_res γ ts res).
  Proof. destruct res; apply _. Qed.

  Definition txn_inv γ : iProp Σ :=
    ∃ (ts : nat) (future past : list action)
      (txns_cmt txns_abt : gmap nat dbmap)
      (resm : gmap nat txnres) (wrsm : gmap nat dbmap)
      (kmodls kmodcs : gmap dbkey dbkmod),
      (* global timestamp *)
      "Hts"    ∷ ts_auth γ ts ∗
      (* prophecy variable *)
      "Hproph" ∷ txn_proph γ future ∗
      (* transaction result map *)
      "Hresm" ∷ txnres_auth γ resm ∗
      (* transaction write set map *)
      "Hwrsm" ∷ txnwrs_auth γ wrsm ∗
      (* key modifications *)
      "Hkmodls" ∷ kmods_lnrz γ kmodls ∗
      "Hkmodcs" ∷ kmods_cmtd γ kmodcs ∗
      (* safe commit/abort invariant *)
      "#Hvr"  ∷ ([∗ map] tid ↦ res ∈ resm, valid_res γ tid res) ∗
      (* TODO: for coordinator recovery, add a monotonically growing set of
      active txns; each active txn either appears in [txns_cmt]/[txns_abt] or in
      the result map [resm]. *)
      "%Hcf"   ∷ ⌜conflict_free future txns_cmt⌝ ∗
      "%Hcp"   ∷ ⌜conflict_past future past txns_abt⌝ ∗
      "%Hcip"  ∷ ⌜cmtd_impl_prep resm wrsm⌝ ∗
      "%Htkcl" ∷ ⌜tmods_kmods_consistent txns_cmt kmodls⌝ ∗
      "%Htkcc" ∷ ⌜tmods_kmods_consistent (resm_to_tmods resm) kmodcs⌝.

End inv.
