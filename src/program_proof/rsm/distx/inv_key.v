From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.distx Require Import base res.
From Perennial.program_proof.rsm.pure Require Import extend.

(** Global per-key/tuple invariant. *)

Definition diff_by_cmtd
  (repl cmtd : list dbval) (kmod : dbkmod) (ts : nat) :=
  match kmod !! ts with
  | Some v => cmtd = last_extend ts repl ++ [v]
  | None => (∃ ts', repl = last_extend ts' cmtd) ∧
           (ts ≠ O -> length repl ≤ ts)%nat
  end.

Definition diff_by_lnrz (cmtd lnrz : list dbval) (txns : dbkmod) : Prop.
Admitted.

Section def.
  Context `{!distx_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : distx_names).

  Definition key_inv_prop
    (key : dbkey) (dbv : dbval) (lnrz cmtd repl : dbhist)
    (tslb tsprep : nat) (kmodl kmodc : dbkmod) : iProp Σ :=
    "%Hlast"    ∷ ⌜last lnrz = Some dbv⌝ ∗
    "%Hprefix"  ∷ ⌜prefix cmtd lnrz⌝ ∗
    "%Hext"     ∷ ⌜(length lnrz ≤ S tslb)%nat⌝ ∗
    "%Hdiffl"   ∷ ⌜diff_by_lnrz cmtd lnrz kmodl⌝ ∗
    "%Hdiffc"   ∷ ⌜diff_by_cmtd repl cmtd kmodc tsprep⌝ ∗
    "%Hzrsv"    ∷ ⌜kmodc !! O = None⌝.

  Definition key_inv γ (key : dbkey) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd repl : dbhist)
      (tslb tsprep : nat) (kmodl kmodc : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_half γ key lnrz ∗
      "Hrepl"     ∷ hist_repl_half γ key repl ∗
      "Htsprep"   ∷ ts_repl_half γ key tsprep ∗
      "Hkmodl"    ∷ kmod_lnrz γ key kmodl ∗
      "Hkmodc"    ∷ kmod_cmtd γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "Hprop"     ∷ key_inv_prop key dbv lnrz cmtd repl tslb tsprep kmodl kmodc.

  Definition key_inv_no_repl_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd : dbhist) (tslb : nat) (kmodl kmodc : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_half γ key lnrz ∗
      "Hkmodl"    ∷ kmod_lnrz γ key kmodl ∗
      "Hkmodc"    ∷ kmod_cmtd γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "Hprop"     ∷ key_inv_prop key dbv lnrz cmtd repl tslb tsprep kmodl kmodc.

  Definition key_inv_with_kmodc_no_repl_tsprep
    γ (key : dbkey) (kmodc : dbkmod) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd : dbhist) (tslb : nat) (kmodl : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_half γ key lnrz ∗
      "Hkmodl"    ∷ kmod_lnrz γ key kmodl ∗
      "Hkmodc"    ∷ kmod_cmtd γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "Hprop"     ∷ key_inv_prop key dbv lnrz cmtd repl tslb tsprep kmodl kmodc.

  (* TODO: better naming. *)

  Definition key_inv_xcmted_no_repl_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) (ts : nat) : iProp Σ :=
    ∃ kmodc,
      "Hkey" ∷ key_inv_with_kmodc_no_repl_tsprep γ key kmodc repl tsprep ∗
      "%Hnc" ∷ ⌜kmodc !! ts = None⌝.

  Definition key_inv_cmted_no_repl_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) (v : dbval) : iProp Σ :=
    ∃ kmodc,
      "Hkey" ∷ key_inv_with_kmodc_no_repl_tsprep γ key kmodc repl tsprep ∗
      "%Hv"  ∷ ⌜kmodc !! tsprep = Some v⌝.

  Definition key_inv_prepared_no_repl_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    ∃ kmodc,
      "Hkey" ∷ key_inv_with_kmodc_no_repl_tsprep γ key kmodc repl tsprep ∗
      "%Hnc" ∷ ⌜kmodc !! tsprep = None⌝.

End def.

Section lemma.
  Context `{!distx_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : distx_names).

  (* TODO: might not need these anymore once update the learn_prepare proof to
  be more consistent with that of learn_commit. *)
  Definition keys_except_group gid (keys : gset dbkey) :=
    filter (λ x, key_to_group x ≠ gid) keys.

  Lemma keys_inv_group {γ keys} gid :
    ([∗ set] key ∈ keys, key_inv γ key) -∗
    ([∗ set] key ∈ (keys_group gid keys), key_inv γ key) ∗
    ([∗ set] key ∈ (keys_except_group gid keys), key_inv γ key).
  Proof.
  Admitted.

  Lemma keys_inv_ungroup {γ keys} gid :
    ([∗ set] key ∈ (keys_group gid keys), key_inv γ key) -∗
    ([∗ set] key ∈ (keys_except_group gid keys), key_inv γ key) -∗
    ([∗ set] key ∈ keys, key_inv γ key).
  Proof.
  Admitted.
  (* TODO: might not need these anymore. *)

  Lemma key_inv_extract_repl_tsprep {γ} key :
    key_inv γ key -∗
    ∃ tpl, key_inv_no_repl_tsprep γ key tpl.1 tpl.2 ∗ tuple_repl_half γ key tpl.
  Proof.
    iIntros "Hkey".
    iNamed "Hkey". iNamed "Hprop".
    rewrite /tuple_repl_half.
    iExists (repl, tsprep).
    iFrame "∗ # %".
  Qed.

  Lemma keys_inv_extract_repl_tsprep {γ} keys :
    ([∗ set] key ∈ keys, key_inv γ key) -∗
    ∃ tpls, ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) ∗
            ([∗ map] key ↦ tpl ∈ tpls, tuple_repl_half γ key tpl) ∧
            ⌜dom tpls = keys⌝.
  Proof.
    iIntros "Hkeys".
    iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
    { iIntros (k Hk) "Hkey". iApply (key_inv_extract_repl_tsprep with "Hkey"). }
    iDestruct (big_sepS_exists_sepM with "Hkeys") as (tpls Hdom) "Htpls".
    iDestruct (big_sepM_sep with "Htpls") as "[Hkeys Htpls]".
    by iFrame.
  Qed.

  Lemma key_inv_merge_repl_tsprep {γ} key tpl :
    key_inv_no_repl_tsprep γ key tpl.1 tpl.2 -∗
    tuple_repl_half γ key tpl -∗
    key_inv γ key.
  Proof.
    iIntros "Hkey Htpl".
    iNamed "Hkey". iDestruct "Htpl" as "[Hhist Hts]".
    iFrame "∗ #".
  Qed.

  Lemma keys_inv_merge_repl_tsprep {γ tpls} keys :
    dom tpls = keys ->
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) -∗
    ([∗ map] key ↦ tpl ∈ tpls, tuple_repl_half γ key tpl) -∗
    ([∗ set] key ∈ keys, key_inv γ key).
  Proof.
    iIntros (Hdom) "Hkeys Htpls".
    iDestruct (big_sepM_sep_2 with "Hkeys Htpls") as "Htpls".
    rewrite -Hdom -big_sepM_dom.
    iApply (big_sepM_mono with "Htpls").
    iIntros (k t Ht) "[Hkey Htpl]".
    iApply (key_inv_merge_repl_tsprep with "Hkey Htpl").
  Qed.

  Lemma key_inv_no_repl_tsprep_unseal_kmodc γ key repl tsprep :
    key_inv_no_repl_tsprep γ key repl tsprep -∗
    ∃ kmodc, key_inv_with_kmodc_no_repl_tsprep γ key kmodc repl tsprep.
  Proof. iIntros "Hkey". iNamed "Hkey". iFrame "% # ∗". Qed.

End lemma.
