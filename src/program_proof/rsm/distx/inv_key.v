From stdpp Require Import list.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.distx Require Import base res.
From Perennial.program_proof.rsm.pure Require Import
  list extend largest_before.

(** Global per-key/tuple invariant. *)

Definition ext_by_cmtd
  (repl cmtd : dbhist) (kmod : dbkmod) (ts : nat) :=
  match kmod !! ts with
  | Some v => cmtd = last_extend ts repl ++ [v]
  | None => (∃ ts', repl = last_extend ts' cmtd) ∧
           (ts ≠ O -> length repl ≤ ts)%nat
  end.

Lemma ext_by_cmtd_prefix {repl cmtd kmod ts} :
  ext_by_cmtd repl cmtd kmod ts ->
  prefix repl cmtd ∨ prefix cmtd repl.
Proof.
  rewrite /ext_by_cmtd.
  intros Hext.
  destruct (kmod !! ts) as [v |].
  - left. rewrite Hext. apply prefix_app_r, last_extend_prefix.
  - right. destruct Hext as [[tsr Hext] _]. rewrite Hext. apply last_extend_prefix.
Qed.

Definition prev_dbval (ts : nat) (d : dbval) (kmod : dbkmod) :=
  match largest_before ts (dom kmod) with
  | Some t => match kmod !! t with
             | Some v => v
             | None => d (* impossible case *)
             end
  | None => d
  end.

Lemma prev_dbval_lt_all ts d kmod :
  lt_all ts (dom kmod) ->
  prev_dbval ts d kmod = d.
Proof.
  intros Hlts.
  rewrite /prev_dbval.
  destruct (largest_before _ _) as [t |] eqn:Hlargest; last done.
  exfalso.
  apply largest_before_Some in Hlargest as (Hin & Ht & _).
  specialize (Hlts _ Hin). simpl in Hlts.
  lia.
Qed.

Lemma prev_dbval_lookup ts v d kmod :
  kmod !! ts = Some v ->
  prev_dbval ts d kmod = v.
Proof.
  intros Hv.
  rewrite /prev_dbval largest_before_elem_of; last first.
  { by rewrite elem_of_dom. }
  by rewrite Hv.
Qed.

Lemma prev_dbval_delete ts tsx v d kmod :
  (ts ≤ tsx)%nat ->
  le_all ts (dom kmod) ->
  kmod !! ts = Some v ->
  prev_dbval tsx v (delete ts kmod) = prev_dbval tsx d kmod.
Proof.
  intros Htsx Hles Hv.
  rewrite /prev_dbval dom_delete_L.
  destruct (largest_before tsx (dom kmod ∖ {[ ts ]})) as [p |] eqn:Hdiff.
  { (* Case: ∃ p ∈ dom kmod ∖ {[ts]}, p ≤ tsx. *)
    rewrite Hdiff.
    replace (largest_before tsx (dom kmod)) with (Some p); last first.
    { by rewrite -Hdiff largest_before_difference_min. }
    apply largest_before_Some in Hdiff as [Hpin _].
    rewrite -dom_delete_L elem_of_dom lookup_delete_is_Some in Hpin.
    destruct Hpin as [Hne [u Hu]].
    rewrite lookup_delete_ne; last done.
    by rewrite Hu.
  }
  (* Case: ∀ n ∈ dom kmod ∖ {[ts]}, tsx < n. *)
  destruct (largest_before tsx (dom kmod)) as [p |] eqn:Hp; last first.
  { (* Case: ∀ n ∈ dom kmod, tsx < n. *)
    (* Above ∧ ts ∈ dom kmod -> tsx < ts, contradicted to ts ≤ tsx. *)
    exfalso.
    apply largest_before_None in Hp.
    apply elem_of_dom_2 in Hv.
    specialize (Hp _ Hv). simpl in Hp.
    lia.
  }
  (* Case: ∃ p ∈ dom kmod, p ≤ tsx. In this case p = ts. *)
  rewrite Hdiff.
  replace p with ts; last first.
  { apply largest_before_None in Hdiff.
    apply largest_before_Some in Hp as (Hin & Hle & Hout).
    apply dec_stable. intros Hne.
    assert (Hindiff : p ∈ dom kmod ∖ {[ ts ]}).
    { by rewrite elem_of_difference not_elem_of_singleton. }
    specialize (Hdiff _ Hindiff). simpl in Hdiff.
    lia.
  }
  by rewrite Hv.
Qed.

Lemma prev_dbval_insert ts tsx v d kmod :
  (tsx < ts)%nat ->
  gt_all ts (dom kmod) ->
  prev_dbval tsx d (<[ts := v]> kmod) = prev_dbval tsx d kmod.
Proof.
  intros Htsx Hgt.
  rewrite /prev_dbval dom_insert_L largest_before_union_max; [| apply Htsx | apply Hgt].
  destruct (largest_before _ _) as [p |] eqn:Hp; last done.
  rewrite lookup_insert_ne; first done.
  intros Htsp. subst p.
  apply largest_before_Some in Hp as [Hin _].
  specialize (Hgt _ Hin). simpl in Hgt.
  lia.
Qed.

Lemma prev_dbval_ge ts tsx d kmod :
  (ts ≤ tsx)%nat ->
  ge_all ts (dom kmod) ->
  prev_dbval tsx d kmod = prev_dbval ts d kmod.
Proof.
  intros Hle Hge.
  rewrite /prev_dbval.
  destruct (largest_before ts (dom kmod)) as [p |] eqn:Hts; last first.
  { apply largest_before_None in Hts.
    destruct (largest_before tsx (dom kmod)) as [q |] eqn:Htsx; last done.
    exfalso.
    apply largest_before_Some in Htsx as [Hq _].
    specialize (Hge _ Hq). simpl in Hge.
    specialize (Hts _ Hq). simpl in Hts.
    lia.
  }
  apply largest_before_Some in Hts as Hp.
  destruct Hp as (Hpin & Hple & Hpout).
  rewrite (largest_before_ge_max _ p); [done | lia | done |].
  intros x Hx.
  specialize (Hpout _ Hx). simpl in Hpout.
  specialize (Hge _ Hx). simpl in Hge.
  lia.
Qed.

Lemma prefix_pointwise {A} (l1 l2 : list A) :
  (∀ i, (i < length l1)%nat -> l1 !! i = l2 !! i) ->
  prefix l1 l2.
Proof.
  intros Hpoint.
  rewrite -(take_drop (length l1) l2).
  exists (drop (length l1) l2).
  rewrite app_inv_tail_iff.
  apply list_eq.
  intros i.
  destruct (decide (i < length l1)%nat) as [Hlt | Hge]; last first.
  { apply not_lt in Hge.
    rewrite lookup_take_ge; last done.
    by rewrite lookup_ge_None_2.
  }
  specialize (Hpoint _ Hlt).
  by rewrite lookup_take_lt.
Qed.

(** Invariant: The linearized history is extended by linearized but not yet
committed txns. *)

Definition ext_by_lnrz (cmtd lnrz : dbhist) (kmodl : dbkmod) :=
  ∃ (vlast : dbval),
    prefix cmtd lnrz ∧
    last cmtd = Some vlast ∧
    set_Forall (λ t, length cmtd ≤ t < length lnrz)%nat (dom kmodl) ∧
    ∀ (t : nat) (u : dbval), (pred (length cmtd) ≤ t)%nat ->
                           lnrz !! t = Some u ->
                           prev_dbval t vlast kmodl = u.

(* Note the [pred] in the last condition, which poses constraints on not just
the additional entries of [lnrz], but also the last overlapping entry between
[cmtd] and [lnrz]. This allows proving invariance of [ext_by_lnrz]
w.r.t. linearize actions without considering [cmtd = lnrz] as a special case. *)

Lemma ext_by_lnrz_not_nil cmtd lnrz kmod :
  ext_by_lnrz cmtd lnrz kmod ->
  cmtd ≠ [].
Proof. intros (v & _ & Hlast & _) Hcmtd. by rewrite Hcmtd in Hlast. Qed.

Section def.
  Context `{!distx_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : distx_names).

  Definition key_inv_prop
    (key : dbkey) (dbv : dbval) (lnrz cmtd repl : dbhist)
    (tslb tsprep : nat) (kmodl kmodc : dbkmod) : iProp Σ :=
    "%Hall"     ∷ ⌜key ∈ keys_all⌝ ∗
    "%Hlast"    ∷ ⌜last lnrz = Some dbv⌝ ∗
    "%Hext"     ∷ ⌜(length lnrz ≤ S tslb)%nat⌝ ∗
    "%Hdiffl"   ∷ ⌜ext_by_lnrz cmtd lnrz kmodl⌝ ∗
    "%Hdiffc"   ∷ ⌜ext_by_cmtd repl cmtd kmodc tsprep⌝ ∗
    "%Hzrsv"    ∷ ⌜kmodc !! O = None⌝.

  Definition key_inv γ (key : dbkey) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd repl : dbhist)
      (tslb tsprep : nat) (kmodl kmodc : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_auth γ key lnrz ∗
      "Hcmtd"     ∷ hist_cmtd_auth γ key cmtd ∗
      "Hrepl"     ∷ hist_repl_half γ key repl ∗
      "Htsprep"   ∷ ts_repl_half γ key tsprep ∗
      "Hkmodl"    ∷ kmod_lnrz_half γ key kmodl ∗
      "Hkmodc"    ∷ kmod_cmtd_half γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "Hprop"     ∷ key_inv_prop key dbv lnrz cmtd repl tslb tsprep kmodl kmodc.

  Definition key_inv_with_kmodl γ (key : dbkey) (kmodl : dbkmod) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd repl : dbhist)
      (tslb tsprep : nat) (kmodc : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_auth γ key lnrz ∗
      "Hcmtd"     ∷ hist_cmtd_auth γ key cmtd ∗
      "Hrepl"     ∷ hist_repl_half γ key repl ∗
      "Htsprep"   ∷ ts_repl_half γ key tsprep ∗
      "Hkmodl"    ∷ kmod_lnrz_half γ key kmodl ∗
      "Hkmodc"    ∷ kmod_cmtd_half γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "Hprop"     ∷ key_inv_prop key dbv lnrz cmtd repl tslb tsprep kmodl kmodc.

  Definition key_inv_with_tslb_no_kmodl
    γ (key : dbkey) (tslb : nat) (kmodl : dbkmod) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd repl : dbhist)
      (tsprep : nat) (kmodc : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_auth γ key lnrz ∗
      "Hcmtd"     ∷ hist_cmtd_auth γ key cmtd ∗
      "Hrepl"     ∷ hist_repl_half γ key repl ∗
      "Htsprep"   ∷ ts_repl_half γ key tsprep ∗
      "Hkmodc"    ∷ kmod_cmtd_half γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "Hprop"     ∷ key_inv_prop key dbv lnrz cmtd repl tslb tsprep kmodl kmodc.

  Definition key_inv_with_tslb γ (key : dbkey) (tslb : nat) : iProp Σ :=
    ∃ (kmodl : dbkmod),
      "Hkey"   ∷ key_inv_with_tslb_no_kmodl γ key tslb kmodl ∗
      "Hkmodl" ∷ kmod_lnrz_half γ key kmodl.

  Definition key_inv_no_kmodl γ (key : dbkey) (kmodl : dbkmod) : iProp Σ :=
    ∃ (tslb : nat), "Hkey" ∷ key_inv_with_tslb_no_kmodl γ key tslb kmodl.

  Definition key_inv_no_repl_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd : dbhist) (tslb : nat) (kmodl kmodc : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_auth γ key lnrz ∗
      "Hcmtd"     ∷ hist_cmtd_auth γ key cmtd ∗
      "Hkmodl"    ∷ kmod_lnrz_half γ key kmodl ∗
      "Hkmodc"    ∷ kmod_cmtd_half γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "Hprop"     ∷ key_inv_prop key dbv lnrz cmtd repl tslb tsprep kmodl kmodc.

  Definition key_inv_with_kmodc_no_repl_tsprep
    γ (key : dbkey) (kmodc : dbkmod) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd : dbhist) (tslb : nat) (kmodl : dbkmod),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_auth γ key lnrz ∗
      "Hcmtd"     ∷ hist_cmtd_auth γ key cmtd ∗
      "Hkmodl"    ∷ kmod_lnrz_half γ key kmodl ∗
      "Hkmodc"    ∷ kmod_cmtd_half γ key kmodc ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "Hprop"     ∷ key_inv_prop key dbv lnrz cmtd repl tslb tsprep kmodl kmodc.

  Definition key_inv_with_tsprep_no_kmodl_kmodc
    γ (key : dbkey) (tsprep : nat) (kmodl kmodc : dbkmod) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd repl : dbhist) (tslb : nat),
      "Hdbv"      ∷ db_ptsto γ key dbv ∗
      "Hlnrz"     ∷ hist_lnrz_auth γ key lnrz ∗
      "Hcmtd"     ∷ hist_cmtd_auth γ key cmtd ∗
      "Hrepl"     ∷ hist_repl_half γ key repl ∗
      "Htsprep"   ∷ ts_repl_half γ key tsprep ∗
      "#Htslb"    ∷ ts_lb γ tslb ∗
      "Hprop"     ∷ key_inv_prop key dbv lnrz cmtd repl tslb tsprep kmodl kmodc.

  Definition key_inv_no_kmodl_kmodc
    γ (key : dbkey) (kmodl kmodc : dbkmod) : iProp Σ :=
    ∃ (tsprep : nat), key_inv_with_tsprep_no_kmodl_kmodc γ key tsprep kmodl kmodc.

  Definition key_inv_with_tsprep
    γ (key : dbkey) (tsprep : nat) : iProp Σ :=
    ∃ (repl : dbhist),
      "Hkey"    ∷ key_inv_no_repl_tsprep γ key repl tsprep ∗
      "Hrepl"   ∷ hist_repl_half γ key repl ∗
      "Htsprep" ∷ ts_repl_half γ key tsprep.

  Definition key_inv_with_repl_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    "Hkey"    ∷ key_inv_no_repl_tsprep γ key repl tsprep ∗
    "Hrepl"   ∷ hist_repl_half γ key repl ∗
    "Htsprep" ∷ ts_repl_half γ key tsprep.    

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

  (* TODO: rename to expose *)
  Lemma key_inv_unseal_tsprep γ key :
    key_inv γ key -∗
    ∃ tsprep, key_inv_with_tsprep γ key tsprep.
  Proof. iIntros "Hkey". iNamed "Hkey". iFrame "∗ #". Qed.

  Lemma key_inv_expose_kmodl γ key :
    key_inv γ key -∗
    ∃ kmodl, key_inv_with_kmodl γ key kmodl.
  Proof. iIntros "Hkey". iNamed "Hkey". iFrame "∗ #". Qed.

  Lemma key_inv_hide_kmodl γ key kmodl :
    key_inv_with_kmodl γ key kmodl -∗
    key_inv γ key.
  Proof. iIntros "Hkey". iNamed "Hkey". iFrame "∗ #". Qed.

  Lemma keys_inv_with_tsprep_extract_kmodl_kmodc {γ} keys tsprep :
    ([∗ set] key ∈ keys, key_inv_with_tsprep γ key tsprep) -∗
    ∃ kmodls kmodcs : gmap dbkey dbkmod,
      ([∗ map] key ↦ kmodl; kmodc ∈ kmodls; kmodcs,
         key_inv_with_tsprep_no_kmodl_kmodc γ key tsprep kmodl kmodc) ∗
      ([∗ map] key ↦ kmodl ∈ kmodls, kmod_lnrz_half γ key kmodl) ∗
      ([∗ map] key ↦ kmodc ∈ kmodcs, kmod_cmtd_half γ key kmodc) ∧
      ⌜dom kmodls = keys⌝.
  Proof.
  Admitted.

  Lemma keys_inv_with_tslb_extract_kmodl {γ} tslbm :
    ([∗ map] key ↦ tslb ∈ tslbm, key_inv_with_tslb γ key tslb) -∗
    ∃ kmodls : gmap dbkey dbkmod,
      ([∗ map] key ↦ tslb;kmodl ∈ tslbm;kmodls, key_inv_with_tslb_no_kmodl γ key tslb kmodl) ∗
      ([∗ map] key ↦ kmodl ∈ kmodls, kmod_lnrz_half γ key kmodl).
  Proof.
  Admitted.

End lemma.
