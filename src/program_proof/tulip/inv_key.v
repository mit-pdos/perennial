From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm Require Import big_sep.
From Perennial.program_proof.rsm.pure Require Import list extend largest_before quorum.
From Perennial.program_proof.tulip Require Import base res.

(** Global per-key/tuple invariant. *)

(* TODO: when adding quorum read, the None branch would have to updated to say
[cmtd = last_extend tsrd repl], and we need an additional invariant that says if
cmtd is longer than repl, then some quourm of replicas must have promised not to
prepare between end of repl to end of cmtd. *)
Definition ext_by_cmtd
  (repl cmtd : dbhist) (kmod : dbkmod) (pts : nat) :=
  match kmod !! pts with
  | Some v => cmtd = last_extend pts repl ++ [v] ∧ (length repl ≤ pts)%nat
  | None => ∃ rts, cmtd = last_extend rts repl ∧ (pts ≠ O -> length cmtd ≤ pts)%nat
  end.

Lemma ext_by_cmtd_impl_prefix_repl_cmtd {repl cmtd kmod ts} :
  ext_by_cmtd repl cmtd kmod ts ->
  prefix repl cmtd.
Proof.
  rewrite /ext_by_cmtd.
  intros Hext.
  destruct (kmod !! ts) as [v |].
  { destruct Hext as [-> _]. apply prefix_app_r, last_extend_prefix. }
  destruct Hext as (rts & -> & _).
  apply last_extend_prefix.
Qed.

Lemma ext_by_cmtd_length_cmtd repl cmtd kmodc pts :
  pts ≠ O ->
  kmodc !! pts = None ->
  ext_by_cmtd repl cmtd kmodc pts ->
  (length cmtd ≤ pts)%nat.
Proof.
  intros Hnz Hnone Hext.
  rewrite /ext_by_cmtd Hnone in Hext.
  destruct Hext as (rts & -> & Hlen).
  by specialize (Hlen Hnz).
Qed.

Lemma ext_by_cmtd_length_repl repl cmtd kmodc pts :
  pts ≠ O ->
  ext_by_cmtd repl cmtd kmodc pts ->
  (length repl ≤ pts)%nat.
Proof.
  intros Hnz Hext.
  rewrite /ext_by_cmtd in Hext.
  destruct (kmodc !! pts) as [v |].
  { by destruct Hext as [_ ?]. }
  destruct Hext as (rts & -> & Hlen).
  specialize (Hlen Hnz).
  etrans; last apply Hlen.
  apply last_extend_length_ge.
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

Lemma prev_dbval_lookup_None ts d kmod :
  kmod !! ts = None ->
  prev_dbval ts d kmod = prev_dbval (pred ts) d kmod.
Proof.
  intros Hnone.
  rewrite /prev_dbval.
  by rewrite largest_before_not_elem_of; last apply not_elem_of_dom.
Qed.

Lemma prev_dbval_empty t d :
  prev_dbval t d ∅ = d.
Proof. by rewrite /prev_dbval largest_before_empty. Qed.

Lemma prev_dbval_outside ts1 ts2 d kmod :
  (ts1 ≤ ts2)%nat ->
  outside_all ts1 ts2 (dom kmod) ->
  prev_dbval ts1 d kmod = prev_dbval ts2 d kmod.
Proof.
  intros Hle Houtside.
  induction ts2 as [| t IH].
  { replace ts1 with O; [done | lia]. }
  destruct (decide (ts1 = S t)) as [-> | Hne]; first done.
  rewrite (prev_dbval_lookup_None (S t)); last first.
  { rewrite -not_elem_of_dom.
    intros Hin.
    specialize (Houtside _ Hin). simpl in Houtside.
    clear -Houtside Hle Hne. lia.
  }
  apply IH.
  { clear -Hle Hne. lia. }
  { intros tx Htx.
    specialize (Houtside _ Htx). simpl in Houtside.
    clear -Houtside. lia.
  }
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

(** Note the [pred] in the last condition, which poses constraints on not just
the additional entries of [lnrz], but also the last overlapping entry between
[cmtd] and [lnrz]. This allows proving invariance of [ext_by_lnrz]
w.r.t. linearize actions without considering [cmtd = lnrz] as a special case. *)

Lemma ext_by_lnrz_impl_cmtd_not_nil cmtd lnrz kmod :
  ext_by_lnrz cmtd lnrz kmod ->
  cmtd ≠ [].
Proof. intros (v & _ & Hlast & _) Hcmtd. by rewrite Hcmtd in Hlast. Qed.

Lemma ext_by_lnrz_impl_prefix_cmtd_lnrz cmtd lnrz kmod :
  ext_by_lnrz cmtd lnrz kmod ->
  prefix cmtd lnrz.
Proof. intros Hext. by destruct Hext as (? & ? & _). Qed.

Lemma ext_by_cmtd_partial_impl_repl_not_nil repl cmtd kmod pts :
  cmtd ≠ [] ->
  kmod !! pts = None ->
  ext_by_cmtd repl cmtd kmod pts ->
  repl ≠ [].
Proof.
  intros Hnnil Hnone Hext.
  rewrite /ext_by_cmtd Hnone in Hext.
  destruct Hext as (rts & Hext & _).
  rewrite Hext in Hnnil.
  by eapply last_extend_not_nil_inv.
Qed.

Definition cmtd_yield_from_kmodc (cmtd : dbhist) (kmodc : dbkmod) :=
  ∀ (t : nat), (t < length cmtd)%nat -> cmtd !! t = Some (prev_dbval t None kmodc).

Section def.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  Definition quorum_validation_fixed_before γ key ts : iProp Σ :=
    ∃ ridsq,
      ([∗ set] rid ∈ ridsq,
         is_replica_key_validation_length_lb γ (key_to_group key) rid key ts) ∧
      ⌜cquorum rids_all ridsq⌝.

  Definition quorum_invalidated_key γ key ts : iProp Σ :=
    ∃ ridsq,
      ([∗ set] rid ∈ ridsq,
         is_replica_key_invalidated_at γ (key_to_group key) rid key ts) ∧
      ⌜cquorum rids_all ridsq⌝.

  Definition quorum_validated_key γ key ts : iProp Σ :=
    ∃ (ridsq : gset u64),
      ([∗ set] rid ∈ ridsq,
         is_replica_key_validated_at γ (key_to_group key) rid key ts) ∧
      ⌜cquorum rids_all ridsq⌝.

  (** This predicate allows proving invariance w.r.t. prepare. In more detail,
  at the time [ts] prepare, an important fact to establish is that the prepare
  timestamp must be gt the largest commit timestamp, and ge the largest read
  timestamp (see the [None] branch of [ext_by_cmtd] for how this is
  encoded). For the case where [ts < pred (length cmtd)], contradiction can be
  derived with the [quorum_validation_fixed_before] predicate. The problematic
  case is [ts = pred (length cmtd)], since the overlapped replica can indeed be
  validated by [ts], and we cannot derive contradiction without the help of this
  predicate. This predicate says that if [cmtd] has been extended to [ts], but
  [ts] has not committed, then it can only be extended by some reader with a
  larger timestamp, which would allow us to derive contradiction in the
  problematic case mentioned above. *)
  Definition committed_or_quorum_invalidated_key γ key (kmodc : dbkmod) ts : iProp Σ :=
    match kmodc !! ts with
    | None => quorum_invalidated_key γ key ts ∨ is_group_aborted γ (key_to_group key) ts
    | _ => True
    end.

  Definition key_inv_internal
    γ (key : dbkey) (tslb : nat) (repl : dbhist) (tsprep : nat) (kmodl kmodc : dbkmod) : iProp Σ :=
    ∃ (dbv : dbval) (lnrz cmtd : dbhist),
      "Hdbv"     ∷ own_db_ptsto γ key dbv ∗
      "Hlnrz"    ∷ own_lnrz_hist γ key lnrz ∗
      "Hcmtd"    ∷ own_cmtd_hist γ key cmtd ∗
      "#Hqvfb"   ∷ quorum_validation_fixed_before γ key (length cmtd) ∗
      "#Hcori"   ∷ committed_or_quorum_invalidated_key γ key kmodc (pred (length cmtd)) ∗
      "#Hqvk"    ∷ ([∗ map] ts ↦ _ ∈ kmodc, quorum_validated_key γ key ts) ∗
      "#Htslb"   ∷ is_largest_ts_lb γ tslb ∗
      "%Hall"    ∷ ⌜key ∈ keys_all⌝ ∗
      "%Hlast"   ∷ ⌜last lnrz = Some dbv⌝ ∗
      "%Hext"    ∷ ⌜(length lnrz ≤ S tslb)%nat⌝ ∗
      "%Hrnnil"  ∷ ⌜repl ≠ []⌝ ∗
      (* TODO: the one above is implied by the one below *)
      "%Hrfirst" ∷ ⌜repl !! O = Some None⌝ ∗
      "%Hdiffl"  ∷ ⌜ext_by_lnrz cmtd lnrz kmodl⌝ ∗
      "%Hdiffc"  ∷ ⌜ext_by_cmtd repl cmtd kmodc tsprep⌝ ∗
      "%Hltlenc" ∷ ⌜gt_all (length cmtd) (dom kmodc)⌝ ∗
      "%Hyield"  ∷ ⌜cmtd_yield_from_kmodc cmtd kmodc⌝ ∗
      "%Hzrsv"   ∷ ⌜kmodc !! O = None⌝.

  Definition key_inv γ (key : dbkey) : iProp Σ :=
    ∃ (tslb : nat) (repl : dbhist) (tsprep : nat) (kmodl kmodc : dbkmod),
      "Hrepl"   ∷ own_repl_hist_half γ key repl ∗
      "Htsprep" ∷ own_repl_ts_half γ key tsprep ∗
      "Hkmodl"  ∷ own_lnrz_kmod_half γ key kmodl ∗
      "Hkmodc"  ∷ own_cmtd_kmod_half γ key kmodc ∗
      "Hkey"    ∷ key_inv_internal γ key tslb repl tsprep kmodl kmodc .

  Definition key_inv_with_kmodl γ (key : dbkey) (kmodl : dbkmod) : iProp Σ :=
    ∃ (tslb : nat) (repl : dbhist) (tsprep : nat) (kmodc : dbkmod),
      "Hrepl"   ∷ own_repl_hist_half γ key repl ∗
      "Htsprep" ∷ own_repl_ts_half γ key tsprep ∗
      "Hkmodl"  ∷ own_lnrz_kmod_half γ key kmodl ∗
      "Hkmodc"  ∷ own_cmtd_kmod_half γ key kmodc ∗
      "Hkey"    ∷ key_inv_internal γ key tslb repl tsprep kmodl kmodc.

  Definition key_inv_with_kmodc_with_kmodl_with_pts
    γ (key : dbkey) (kmodc kmodl : dbkmod) (pts : nat) : iProp Σ :=
    ∃ (tslb : nat) (repl : dbhist),
      "Hrepl"   ∷ own_repl_hist_half γ key repl ∗
      "Htsprep" ∷ own_repl_ts_half γ key pts ∗
      "Hkmodl"  ∷ own_lnrz_kmod_half γ key kmodl ∗
      "Hkmodc"  ∷ own_cmtd_kmod_half γ key kmodc ∗
      "Hkey"    ∷ key_inv_internal γ key tslb repl pts kmodl kmodc.

  Definition key_inv_with_tslb_no_kmodl
    γ (key : dbkey) (tslb : nat) (kmodl : dbkmod) : iProp Σ :=
    ∃ (repl : dbhist) (tsprep : nat) (kmodc : dbkmod),
      "Hrepl"   ∷ own_repl_hist_half γ key repl ∗
      "Htsprep" ∷ own_repl_ts_half γ key tsprep ∗
      "Hkmodc"  ∷ own_cmtd_kmod_half γ key kmodc ∗
      "Hkey"    ∷ key_inv_internal γ key tslb repl tsprep kmodl kmodc.

  Definition key_inv_with_tslb γ (key : dbkey) (tslb : nat) : iProp Σ :=
    ∃ (repl : dbhist) (tsprep : nat) (kmodl kmodc : dbkmod),
      "Hrepl"   ∷ own_repl_hist_half γ key repl ∗
      "Htsprep" ∷ own_repl_ts_half γ key tsprep ∗
      "Hkmodl"  ∷ own_lnrz_kmod_half γ key kmodl ∗
      "Hkmodc"  ∷ own_cmtd_kmod_half γ key kmodc ∗
      "Hkey"    ∷ key_inv_internal γ key tslb repl tsprep kmodl kmodc.

  Definition key_inv_no_kmodl γ (key : dbkey) (kmodl : dbkmod) : iProp Σ :=
    ∃ (tslb : nat) (repl : dbhist) (tsprep : nat) (kmodc : dbkmod),
      "Hrepl"   ∷ own_repl_hist_half γ key repl ∗
      "Htsprep" ∷ own_repl_ts_half γ key tsprep ∗
      "Hkmodc"  ∷ own_cmtd_kmod_half γ key kmodc ∗
      "Hkey"    ∷ key_inv_internal γ key tslb repl tsprep kmodl kmodc.

  Definition key_inv_no_tsprep γ (key : dbkey) (tsprep : nat) : iProp Σ :=
    ∃ (tslb : nat) (repl : dbhist) (kmodl kmodc : dbkmod),
      "Hrepl"   ∷ own_repl_hist_half γ key repl ∗
      "Hkmodl"  ∷ own_lnrz_kmod_half γ key kmodl ∗
      "Hkmodc"  ∷ own_cmtd_kmod_half γ key kmodc ∗
      "Hkey"    ∷ key_inv_internal γ key tslb repl tsprep kmodl kmodc.

  Definition key_inv_no_repl_no_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    ∃ (tslb : nat) (kmodl kmodc : dbkmod),
      "Hkmodl" ∷ own_lnrz_kmod_half γ key kmodl ∗
      "Hkmodc" ∷ own_cmtd_kmod_half γ key kmodc ∗
      "Hkey"   ∷ key_inv_internal γ key tslb repl tsprep kmodl kmodc.

  Definition key_inv_with_kmodc_no_tsprep
    γ (key : dbkey) (kmodc : dbkmod) (tsprep : nat) : iProp Σ :=
    ∃ (tslb : nat) (repl : dbhist) (kmodl : dbkmod),
      "Hrepl"   ∷ own_repl_hist_half γ key repl ∗
      "Hkmodl"  ∷ own_lnrz_kmod_half γ key kmodl ∗
      "Hkmodc"  ∷ own_cmtd_kmod_half γ key kmodc ∗
      "Hkey"    ∷ key_inv_internal γ key tslb repl tsprep kmodl kmodc.

  Definition key_inv_with_kmodc_no_repl_no_tsprep
    γ (key : dbkey) (kmodc : dbkmod) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    ∃ (tslb : nat) (kmodl : dbkmod),
      "Hkmodl" ∷ own_lnrz_kmod_half γ key kmodl ∗
      "Hkmodc" ∷ own_cmtd_kmod_half γ key kmodc ∗
      "Hkey"   ∷ key_inv_internal γ key tslb repl tsprep kmodl kmodc.

  Definition key_inv_with_tsprep_no_kmodl_no_kmodc
    γ (key : dbkey) (tsprep : nat) (kmodl kmodc : dbkmod) : iProp Σ :=
    ∃ (tslb : nat) (repl : dbhist),
      "Hrepl"   ∷ own_repl_hist_half γ key repl ∗
      "Htsprep" ∷ own_repl_ts_half γ key tsprep ∗
      "Hkey"    ∷ key_inv_internal γ key tslb repl tsprep kmodl kmodc.

  Definition key_inv_no_kmodl_no_kmodc
    γ (key : dbkey) (kmodl kmodc : dbkmod) : iProp Σ :=
    ∃ (tslb : nat) (repl : dbhist) (tsprep : nat),
      "Hrepl"   ∷ own_repl_hist_half γ key repl ∗
      "Htsprep" ∷ own_repl_ts_half γ key tsprep ∗
      "Hkey"    ∷ key_inv_internal γ key tslb repl tsprep kmodl kmodc.

  Definition key_inv_with_tsprep
    γ (key : dbkey) (tsprep : nat) : iProp Σ :=
    ∃ (tslb : nat) (repl : dbhist) (kmodl kmodc : dbkmod),
      "Hrepl"   ∷ own_repl_hist_half γ key repl ∗
      "Htsprep" ∷ own_repl_ts_half γ key tsprep ∗
      "Hkmodl"  ∷ own_lnrz_kmod_half γ key kmodl ∗
      "Hkmodc"  ∷ own_cmtd_kmod_half γ key kmodc ∗
      "Hkey"    ∷ key_inv_internal γ key tslb repl tsprep kmodl kmodc.

  Definition key_inv_with_repl_with_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) : iProp Σ :=
    ∃ (tslb : nat) (kmodl kmodc : dbkmod),
      "Hrepl"   ∷ own_repl_hist_half γ key repl ∗
      "Htsprep" ∷ own_repl_ts_half γ key tsprep ∗
      "Hkmodl"  ∷ own_lnrz_kmod_half γ key kmodl ∗
      "Hkmodc"  ∷ own_cmtd_kmod_half γ key kmodc ∗
      "Hkey"    ∷ key_inv_internal γ key tslb repl tsprep kmodl kmodc.

  (* TODO: better naming. *)

  Definition key_inv_xcmted_no_tsprep
    γ (key : dbkey) (tsprep : nat) (ts : nat) : iProp Σ :=
    ∃ kmodc,
      "Hkey" ∷ key_inv_with_kmodc_no_tsprep γ key kmodc tsprep ∗
      "%Hnc" ∷ ⌜kmodc !! ts = None⌝.

  Definition key_inv_cmted_no_repl_tsprep
    γ (key : dbkey) (repl : dbhist) (tsprep : nat) (v : dbval) : iProp Σ :=
    ∃ kmodc,
      "Hkey" ∷ key_inv_with_kmodc_no_repl_no_tsprep γ key kmodc repl tsprep ∗
      "%Hv"  ∷ ⌜kmodc !! tsprep = Some v⌝.

  Definition key_inv_prepared_no_tsprep
    γ (key : dbkey) (tsprep : nat) : iProp Σ :=
    ∃ kmodc,
      "Hkey" ∷ key_inv_with_kmodc_no_tsprep γ key kmodc tsprep ∗
      "%Hnc" ∷ ⌜kmodc !! tsprep = None⌝.

End def.

Section lemma.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  (** Extracting and merging the timestamp lock. Used in the invariance of
  [prepare]. *)

  Lemma key_inv_extract_tsprep {γ} key :
    key_inv γ key -∗
    ∃ ts, key_inv_no_tsprep γ key ts ∗ own_repl_ts_half γ key ts.
  Proof. iNamed 1. iFrame. Qed.

  Lemma keys_inv_extract_tsprep {γ} keys :
    ([∗ set] key ∈ keys, key_inv γ key) -∗
    ∃ tss, ([∗ map] key ↦ ts ∈ tss, key_inv_no_tsprep γ key ts) ∗
           ([∗ map] key ↦ ts ∈ tss, own_repl_ts_half γ key ts) ∧
           ⌜dom tss = keys⌝.
  Proof.
    iIntros "Hkeys".
    iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
    { iIntros (k Hk) "Hkey". iApply (key_inv_extract_tsprep with "Hkey"). }
    iDestruct (big_sepS_exists_sepM with "Hkeys") as (tss Hdom) "Htss".
    iDestruct (big_sepM_sep with "Htss") as "[Hkeys Htss]".
    by iFrame.
  Qed.

  Lemma key_inv_merge_tsprep {γ} key ts :
    key_inv_no_tsprep γ key ts -∗
    own_repl_ts_half γ key ts -∗
    key_inv γ key.
  Proof. iIntros "Hkey Hts". iFrame. Qed.

  Lemma keys_inv_merge_tsprep {γ tss} keys :
    dom tss = keys ->
    ([∗ map] key ↦ ts ∈ tss, key_inv_no_tsprep γ key ts) -∗
    ([∗ map] key ↦ ts ∈ tss, own_repl_ts_half γ key ts) -∗
    ([∗ set] key ∈ keys, key_inv γ key).
  Proof.
    iIntros (Hdom) "Hkeys Htss".
    iDestruct (big_sepM_sep_2 with "Hkeys Htss") as "Htss".
    rewrite -Hdom -big_sepM_dom.
    iApply (big_sepM_mono with "Htss").
    iIntros (k t Ht) "[Hkey Ht]".
    iApply (key_inv_merge_tsprep with "Hkey Ht").
  Qed.

  Lemma key_inv_no_tsprep_unseal_kmodc γ key tsprep :
    key_inv_no_tsprep γ key tsprep -∗
    ∃ kmodc, key_inv_with_kmodc_no_tsprep γ key kmodc tsprep.
  Proof. iNamed 1. iFrame. Qed.

  (** Extracting and merging the replicated tuple (i.e., timestamp lock and
  replicated history). Used in the invariance of [learn_commit]. *)

  Lemma key_inv_extract_repl_pts {γ} key :
    key_inv γ key -∗
    ∃ tpl,
      key_inv_no_repl_no_tsprep γ key tpl.1 tpl.2 ∗ own_repl_tuple_half γ key tpl.
  Proof. iNamed 1. iExists (repl, tsprep). iFrame "∗ # %". Qed.

  Lemma keys_inv_extract_repl_pts {γ} keys :
    ([∗ set] key ∈ keys, key_inv γ key) -∗
    ∃ hists ptsm,
      ([∗ map] key ↦ hist; pts ∈ hists; ptsm, key_inv_no_repl_no_tsprep γ key hist pts) ∗
      ([∗ map] key ↦ hist ∈ hists, own_repl_hist_half γ key hist) ∗
      ([∗ map] key ↦ pts ∈ ptsm, own_repl_ts_half γ key pts) ∗
      ⌜dom hists = keys⌝.
  Proof.
    iIntros "Hkeys".
    iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
    { iIntros (k Hk) "Hkey". iApply (key_inv_extract_repl_pts with "Hkey"). }
    iDestruct (big_sepS_exists_sepM with "Hkeys") as (tpls Hdom) "Hkeys".
    iDestruct (big_sepM_sep with "Hkeys") as "[Hkeys Htpls]".
    rewrite /own_repl_tuple_half.
    iDestruct (big_sepM_sep with "Htpls") as "[Hhists Hptsm]".
    iExists (fst <$> tpls), (snd <$> tpls).
    rewrite big_sepM2_fst_snd.
    iFrame.
    iSplitL "Hhists".
    { iApply (big_sepM_impl_dom_eq with "Hhists"); first by rewrite dom_fmap_L.
      iIntros (k [h t] h' Hht Hh') "!> Hhist".
      rewrite lookup_fmap Hht in Hh'.
      by inv Hh'.
    }
    iSplit.
    { iApply (big_sepM_impl_dom_eq with "Hptsm"); first by rewrite dom_fmap_L.
      iIntros (k [h t] t' Hht Ht') "!> Hptsm".
      rewrite lookup_fmap Hht in Ht'.
      by inv Ht'.
    }
    iPureIntro.
    by rewrite dom_fmap_L.
  Qed.

  Lemma key_inv_merge_repl_pts {γ} key hist pts :
    key_inv_no_repl_no_tsprep γ key hist pts -∗
    own_repl_hist_half γ key hist -∗
    own_repl_ts_half γ key pts -∗
    key_inv γ key.
  Proof. iIntros "Hkey Hhist Hpts". iFrame. Qed.

  Lemma keys_inv_merge_repl_pts {γ histm ptsm} keys :
    dom histm = keys ->
    ([∗ map] key ↦ hist; pts ∈ histm; ptsm, key_inv_no_repl_no_tsprep γ key hist pts) -∗
    ([∗ map] key ↦ hist ∈ histm, own_repl_hist_half γ key hist) -∗
    ([∗ map] key ↦ pts ∈ ptsm, own_repl_ts_half γ key pts) -∗
    ([∗ set] key ∈ keys, key_inv γ key).
  Proof.
    iIntros (Hdom) "Hkeys Hhistm Hptsm".
    iDestruct (big_sepM2_dom with "Hkeys") as %Hdomtpl.
    iDestruct (big_sepM_big_sepM2 _ _ ptsm with "Hhistm") as "Hhistm"; first done.
    iDestruct (big_sepM_big_sepM2 _ _ histm with "Hptsm") as "Hptsm"; first done.
    iDestruct (big_sepM2_flip with "Hptsm") as "Hptsm".
    iDestruct (big_sepM2_sep_2 with "Hhistm Hkeys") as "Hkeys".
    iDestruct (big_sepM2_sep_2 with "Hptsm Hkeys") as "Hkeys".
    rewrite -Hdom -big_sepM_dom.
    iApply (big_sepM2_sepM_impl with "Hkeys"); first done.
    iIntros (k h t h' Hh Ht Hh') "!> (Hpts & Hhist & Hkey)".
    iApply (key_inv_merge_repl_pts with "Hkey Hhist Hpts").
  Qed.

  Lemma key_inv_no_repl_tsprep_unseal_kmodc γ key repl tsprep :
    key_inv_no_repl_no_tsprep γ key repl tsprep -∗
    ∃ kmodc, key_inv_with_kmodc_no_repl_no_tsprep γ key kmodc repl tsprep.
  Proof. iNamed 1. iFrame. Qed.

  Lemma key_inv_expose_tsprep γ key :
    key_inv γ key -∗
    ∃ tsprep, key_inv_with_tsprep γ key tsprep.
  Proof. iNamed 1. iFrame. Qed.

  Lemma key_inv_expose_kmodl γ key :
    key_inv γ key -∗
    ∃ kmodl, key_inv_with_kmodl γ key kmodl.
  Proof. iNamed 1. iFrame. Qed.

  Lemma key_inv_expose_kmodc_kmodl_pts γ key :
    key_inv γ key -∗
    ∃ kmodc kmodl pts, key_inv_with_kmodc_with_kmodl_with_pts γ key kmodc kmodl pts.
  Proof. iNamed 1. iFrame. Qed.

  Lemma key_inv_hide_kmodl γ key kmodl :
    key_inv_with_kmodl γ key kmodl -∗
    key_inv γ key.
  Proof. iNamed 1. iFrame. Qed.

  Lemma key_inv_hide_kmodc_kmodl_pts γ key kmodc kmodl pts :
    key_inv_with_kmodc_with_kmodl_with_pts γ key kmodc kmodl pts -∗
    key_inv γ key.
  Proof. iNamed 1. iFrame. Qed.

  Lemma keys_inv_with_tsprep_extract_kmodl_kmodc {γ} keys tsprep :
    ([∗ set] key ∈ keys, key_inv_with_tsprep γ key tsprep) -∗
    ∃ kmodls kmodcs : gmap dbkey dbkmod,
      ([∗ map] key ↦ kmodl; kmodc ∈ kmodls; kmodcs,
         key_inv_with_tsprep_no_kmodl_no_kmodc γ key tsprep kmodl kmodc) ∗
      ([∗ map] key ↦ kmodl ∈ kmodls, own_lnrz_kmod_half γ key kmodl) ∗
      ([∗ map] key ↦ kmodc ∈ kmodcs, own_cmtd_kmod_half γ key kmodc) ∧
      ⌜dom kmodls = keys⌝.
  Proof.
    iIntros "Hkeys".
    iAssert ([∗ set] key ∈ keys, ∃ (kmodlc : dbkmod * dbkmod),
                key_inv_with_tsprep_no_kmodl_no_kmodc γ key tsprep kmodlc.1 kmodlc.2 ∗
                own_lnrz_kmod_half γ key kmodlc.1 ∗
                own_cmtd_kmod_half γ key kmodlc.2)%I with "[Hkeys]" as "Hkeys".
    { iApply (big_sepS_mono with "Hkeys").
      iIntros (k Hk).
      iNamed 1.
      iExists (kmodl, kmodc).
      iFrame.
    }
    iDestruct (big_sepS_exists_sepM with "Hkeys") as (kmodlcs) "[%Hdom Hkeys]".
    iExists (fmap fst kmodlcs), (fmap snd kmodlcs).
    rewrite 2!big_sepM_sep.
    iDestruct "Hkeys" as "(Hkeys & Hlnrzs & Hcmtds)".
    iSplitL "Hkeys".
    { rewrite big_sepM2_fst_snd. by iApply (big_sepM_mono with "Hkeys"). }
    iSplitL "Hlnrzs".
    { iApply (big_sepM_impl_dom_eq with "Hlnrzs"); first by rewrite dom_fmap_L.
      iIntros (k [kmodl kmodc] kmodl' Hkmodlc Hkmodl') "!> Hlnrz".
      rewrite lookup_fmap Hkmodlc /= in Hkmodl'.
      by inv Hkmodl'.
    }
    iSplitL "Hcmtds".
    { iApply (big_sepM_impl_dom_eq with "Hcmtds"); first by rewrite dom_fmap_L.
      iIntros (k [kmodl kmodc] kmodc' Hkmodlc Hkmodc') "!> Hcmtd".
      rewrite lookup_fmap Hkmodlc /= in Hkmodc'.
      by inv Hkmodc'.
    }
    iPureIntro.
    by rewrite dom_fmap_L.
  Qed.

  Lemma keys_inv_with_tslb_extract_kmodl {γ} tslbm :
    ([∗ map] key ↦ tslb ∈ tslbm, key_inv_with_tslb γ key tslb) -∗
    ∃ kmodls : gmap dbkey dbkmod,
      ([∗ map] key ↦ tslb;kmodl ∈ tslbm;kmodls, key_inv_with_tslb_no_kmodl γ key tslb kmodl) ∗
      ([∗ map] key ↦ kmodl ∈ kmodls, own_lnrz_kmod_half γ key kmodl).
  Proof.
    iIntros "Hkeys".
    iAssert ([∗ map] key ↦ tslb ∈ tslbm, ∃ (kmodl : dbkmod),
                key_inv_with_tslb_no_kmodl γ key tslb kmodl ∗
                own_lnrz_kmod_half γ key kmodl)%I with "[Hkeys]" as "Hkeys".
    { iApply (big_sepM_mono with "Hkeys").
      iIntros (k tslb Htslb).
      iNamed 1.
      iFrame.
    }
    iDestruct (big_sepM_exists_sepM2 with "Hkeys") as (kmodls) "Hkeys".
    iExists kmodls.
    iDestruct (big_sepM2_sep with "Hkeys") as "[Hkeys Hlnrzs]".
    iFrame "Hkeys".
    rewrite big_sepM2_flip.
    iApply (big_sepM_big_sepM2_2 with "Hlnrzs").
  Qed.

End lemma.
