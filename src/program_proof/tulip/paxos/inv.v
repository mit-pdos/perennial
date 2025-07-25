From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm Require Import big_sep.
From Perennial.program_proof.rsm.pure Require Import quorum list extend.
From Perennial.program_proof.tulip.paxos Require Import base consistency msg res recovery.

Section inv.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Definition paxosNS := nroot .@ "paxos".

  Definition nodedec_to_ledger d :=
    match d with
    | Accept v => Some v
    | Reject => None
    end.

  Lemma nodedec_to_ledger_Some_inv d v :
    nodedec_to_ledger d = Some v ->
    d = Accept v.
  Proof. by destruct d; first inv 1. Qed.

  Lemma nodedec_to_ledger_None_inv d :
    nodedec_to_ledger d = None ->
    d = Reject.
  Proof. by destruct d. Qed.

  Definition fixed_proposals (ds : list nodedec) (ps : proposals) :=
    ∀ t d, ds !! t = Some d -> ps !! t = nodedec_to_ledger d.

  Definition free_terms_after (t : nat) (ts : gset nat) :=
    ∀ t', (t < t')%nat -> t' ∉ ts.

  Definition prefix_base_ledger γ t v : iProp Σ :=
    ∃ vlb, is_base_proposal_receipt γ t vlb ∗ ⌜prefix vlb v⌝.

  Definition prefix_growing_ledger γ t v : iProp Σ :=
    ∃ vub, is_proposal_lb γ t vub ∗ ⌜prefix v vub⌝.

  Lemma prefix_growing_ledger_impl_prefix γ t v1 v2 :
    prefix_growing_ledger γ t v1 -∗
    prefix_growing_ledger γ t v2 -∗
    ⌜prefix v1 v2 ∨ prefix v2 v1⌝.
  Proof.
    iIntros "(%vub1 & Hlb1 & %Hprefix1) (%vub2 & Hlb2 & %Hprefix2)".
    iDestruct (proposal_lb_prefix with "Hlb1 Hlb2") as %Hprefix.
    iPureIntro.
    destruct Hprefix as [Hprefix | Hprefix].
    - by apply (prefix_common_ub _ _ vub2); first trans vub1.
    - by apply (prefix_common_ub _ _ vub1); last trans vub2.
  Qed.

  Definition free_termps nid termc :=
    filter (λ t, (termc < t)%nat ∧ is_term_of_node nid t) terms_all.

  Definition safe_ledger_in γ nids t v : iProp Σ :=
    ∃ nid nidsq,
      "#Hvacpt"  ∷ is_accepted_proposal_lb γ nid t v ∗
      "#Hacpt"   ∷ ([∗ set] nid ∈ nidsq, is_accepted_proposal_length_lb γ nid t (length v)) ∗
      "%Hquorum" ∷ ⌜cquorum nids nidsq⌝ ∗
      "%Hmember" ∷ ⌜nid ∈ nids⌝.

  Lemma safe_ledger_in_weaken {γ nids t v} vlb :
    prefix vlb v ->
    safe_ledger_in γ nids t v -∗
    safe_ledger_in γ nids t vlb.
  Proof.
    iIntros (Hprefix) "Hv".
    iNamed "Hv".
    iDestruct (accepted_proposal_lb_weaken vlb with "Hvacpt") as "Hvacpt'".
    { apply Hprefix. }
    set Ψ := λ nid, is_accepted_proposal_length_lb γ nid t (length vlb).
    iDestruct (big_sepS_impl _ Ψ with "Hacpt []") as "Hacpt'".
    { iIntros (nidx Hnidx) "!> Hlenlb".
      iApply (accepted_proposal_length_lb_weaken (length vlb) with "Hlenlb").
      by apply prefix_length.
    }
    iFrame "# %".
  Qed.

  Definition safe_ledger γ nids v : iProp Σ :=
    ∃ t, safe_ledger_in γ nids t v.

  Definition safe_ledger_above γ nids t v : iProp Σ :=
    ∃ t', safe_ledger_in γ nids t' v ∗ ⌜(t' ≤ t)%nat⌝.

  Lemma safe_ledger_above_mono {γ nids} t t' v :
    (t ≤ t')%nat ->
    safe_ledger_above γ nids t v -∗
    safe_ledger_above γ nids t' v.
  Proof. iIntros (Hle) "(%p & Hsafe & %Hp)". iExists p. iFrame. iPureIntro. lia. Qed.

  Lemma safe_ledger_above_weaken {γ nids t v} vlb :
    prefix vlb v ->
    safe_ledger_above γ nids t v -∗
    safe_ledger_above γ nids t vlb.
  Proof.
    iIntros (Hprefix) "(%p & Hv & %Hplet)".
    iDestruct (safe_ledger_in_weaken with "Hv") as "Hvlb".
    { apply Hprefix. }
    by iFrame "Hvlb".
  Qed.

  Definition node_inv γ nids nid terml : iProp Σ :=
    ∃ ds psa termc lsnc logn wal,
      "Hds"      ∷ own_past_nodedecs γ nid ds ∗
      "Hpsa"     ∷ own_accepted_proposals γ nid psa ∗
      "Htermc"   ∷ own_current_term_half γ nid termc ∗
      "Hterml"   ∷ own_ledger_term_half γ nid terml ∗
      "Hlsnc"    ∷ own_committed_lsn_half γ nid lsnc ∗
      "Hlogn"    ∷ own_node_ledger_half γ nid logn ∗
      "Hacpt"    ∷ own_accepted_proposal γ nid terml logn ∗
      "Hlsnps"   ∷ ([∗ set] t ∈ free_termps nid termc, own_free_prepare_lsn γ t) ∗
      "Hwalnode" ∷ own_node_wal_half γ nid wal ∗
      "#Hpsalbs" ∷ ([∗ map] t ↦ v ∈ psa, prefix_base_ledger γ t v) ∗
      "#Hpsaubs" ∷ ([∗ map] t ↦ v ∈ psa, prefix_growing_ledger γ t v) ∗
      "#Hsafel"  ∷ safe_ledger_above γ nids terml (take lsnc logn) ∗
      "%Hfixed"  ∷ ⌜fixed_proposals ds psa⌝ ∗
      "%Hdompsa" ∷ ⌜free_terms_after terml (dom psa)⌝ ∗
      "%Hlends"  ∷ ⌜length ds = termc⌝ ∗
      "%Htermlc" ∷ ⌜(terml ≤ termc)%nat⌝ ∗
      "%Hltlog"  ∷ ⌜(lsnc ≤ length logn)%nat⌝ ∗
      "%Hexec"   ∷ ⌜execute_paxos_cmds wal = PaxosState termc terml lsnc logn⌝.

  Definition node_inv_without_ds_psa
    γ nids nid terml (ds : list nodedec) (psa : proposals) : iProp Σ :=
    ∃ termc lsnc logn wal,
      "Htermc"   ∷ own_current_term_half γ nid termc ∗
      "Hterml"   ∷ own_ledger_term_half γ nid terml ∗
      "Hlogn"    ∷ own_node_ledger_half γ nid logn ∗
      "Hlsnc"    ∷ own_committed_lsn_half γ nid lsnc ∗
      "Hacpt"    ∷ own_accepted_proposal γ nid terml logn ∗
      "Hlsnps"   ∷ ([∗ set] t ∈ free_termps nid termc, own_free_prepare_lsn γ t) ∗
      "Hwalnode" ∷ own_node_wal_half γ nid wal ∗
      "#Hsafel"  ∷ safe_ledger_above γ nids terml (take lsnc logn) ∗
      "%Hdompsa" ∷ ⌜free_terms_after terml (dom psa)⌝ ∗
      "%Hlends"  ∷ ⌜length ds = termc⌝ ∗
      "%Htermlc" ∷ ⌜(terml ≤ termc)%nat⌝ ∗
      "%Hltlog"  ∷ ⌜(lsnc ≤ length logn)%nat⌝ ∗
      "%Hexec"   ∷ ⌜execute_paxos_cmds wal = PaxosState termc terml lsnc logn⌝.

  Definition node_inv_psa γ nid psa : iProp Σ :=
    "Hpsa"     ∷ own_accepted_proposals γ nid psa ∗
    "#Hpsalbs" ∷ ([∗ map] t ↦ v ∈ psa, prefix_base_ledger γ t v) ∗
    "#Hpsaubs" ∷ ([∗ map] t ↦ v ∈ psa, prefix_growing_ledger γ t v).

  Definition node_inv_ds_psa γ nid ds psa : iProp Σ :=
    "Hpsa"    ∷ node_inv_psa γ nid psa ∗
    "Hpastd"  ∷ own_past_nodedecs γ nid ds ∗
    "%Hfixed" ∷ ⌜fixed_proposals ds psa⌝.

  Lemma own_ledger_term_node_inv_terml_eq γ nids nid terml terml' :
    own_ledger_term_half γ nid terml -∗
    node_inv γ nids nid terml' -∗
    ⌜terml' = terml⌝.
  Proof.
    iIntros "HtermlX Hnode".
    iNamed "Hnode".
    by iDestruct (ledger_term_agree with "HtermlX Hterml") as %->.
  Qed.

  Definition equal_latest_longest_proposal_nodedec (dssq : gmap u64 (list nodedec)) t v :=
    equal_latest_longest_proposal_with (mbind nodedec_to_ledger) dssq t v.

  Definition safe_base_proposal γ nids t v : iProp Σ :=
    ∃ dssqlb,
      "#Hdsq"    ∷ ([∗ map] nid ↦ ds ∈ dssqlb, is_past_nodedecs_lb γ nid ds) ∗
      "%Hlen"    ∷ ⌜map_Forall (λ _ ds, (length ds = t)%nat) dssqlb⌝ ∗
      "%Heq"     ∷ ⌜equal_latest_longest_proposal_nodedec dssqlb t v⌝ ∗
      "%Hquorum" ∷ ⌜cquorum nids (dom dssqlb)⌝.

  Definition latest_term_before_nodedec t (ds : list nodedec) :=
    latest_term_before_with (mbind nodedec_to_ledger) t ds.

  Lemma latest_term_before_nodedec_unfold t ds :
    latest_term_before_nodedec t ds = latest_term_before_with (mbind nodedec_to_ledger) t ds.
  Proof. done. Qed.

  Definition latest_term_nodedec ds :=
    latest_term_before_nodedec (length ds) ds.

  Lemma latest_term_nodedec_unfold ds :
    latest_term_nodedec ds = latest_term_before_nodedec (length ds) ds.
  Proof. done. Qed.

  Lemma latest_term_before_nodedec_app t ds dsapp :
    (t ≤ length ds)%nat ->
    latest_term_before_nodedec t (ds ++ dsapp) = latest_term_before_nodedec t ds.
  Proof.
    intros Hlen.
    rewrite /latest_term_before_nodedec.
    induction t as [| t IH]; first done.
    rewrite /= -IH; last lia.
    by rewrite lookup_app_l; last lia.
  Qed.

  Lemma latest_term_nodedec_snoc_Reject ds :
    latest_term_nodedec (ds ++ [Reject]) = latest_term_nodedec ds.
  Proof.
    rewrite /latest_term_nodedec /latest_term_before_nodedec last_length /=.
    rewrite lookup_snoc_length /=.
    by apply latest_term_before_nodedec_app.
  Qed.

  Lemma latest_term_nodedec_extend_Reject t ds :
    latest_term_nodedec (extend t Reject ds) = latest_term_nodedec ds.
  Proof.
    unfold extend.
    induction t as [| t IH]; first by rewrite app_nil_r.
    destruct (decide (t < length ds)%nat) as [Hlt | Hge].
    { replace (t - length ds)%nat with O in IH by lia.
      by replace (S t - length ds)%nat with O by lia.
    }
    replace (S t - length ds)%nat with (S (t - length ds)%nat) by lia.
    by rewrite replicate_S_end assoc latest_term_nodedec_snoc_Reject.
  Qed.

  Lemma fixed_proposals_latest_term_before_nodedec ds psa t :
    (t ≤ length ds)%nat ->
    fixed_proposals ds psa ->
    latest_term_before_nodedec t ds = latest_term_before t psa.
  Proof.
    intros Hlen Hfixed.
    rewrite /latest_term_before_nodedec /latest_term_before.
    induction t as [| p IH]; first done.
    simpl.
    assert (p < length ds)%nat as Hp by lia.
    apply list_lookup_lt in Hp as [d Hd].
    specialize (Hfixed _ _ Hd).
    rewrite Hd /= -Hfixed IH; [done | lia].
  Qed.

  Definition latest_term_before_quorum_nodedec (dss : gmap u64 (list nodedec)) t :=
    latest_term_before_quorum_with (mbind nodedec_to_ledger) dss t.

  Lemma latest_term_before_quorum_nodedec_unfold dss t :
    latest_term_before_quorum_nodedec dss t =
    latest_term_before_quorum_with (mbind nodedec_to_ledger) dss t.
  Proof. done. Qed.

  Lemma latest_term_before_quorum_nodedec_prefixes dss dsslb t :
    map_Forall2 (λ _ dslb ds, prefix dslb ds ∧ (t ≤ length dslb)%nat) dsslb dss ->
    latest_term_before_quorum_nodedec dsslb t = latest_term_before_quorum_nodedec dss t.
  Proof.
    intros Hprefixes.
    rewrite /latest_term_before_quorum_nodedec /latest_term_before_quorum_with.
    f_equal.
    apply map_eq.
    intros nid.
    rewrite 2!lookup_fmap.
    specialize (Hprefixes nid).
    inversion Hprefixes as [dslb ds Hprefix Heq1 Heq2 | ]; [ simpl | done ].
    destruct Hprefix as [[dsapp ->] Hlen].
    f_equal.
    by rewrite -2!latest_term_before_nodedec_unfold latest_term_before_nodedec_app.
  Qed.

  Lemma fixed_proposals_latest_term_before_quorum_nodedec dss (bs : gmap u64 proposals) t :
    map_Forall2 (λ _ ds psa, fixed_proposals ds psa ∧ (t ≤ length ds)%nat) dss bs ->
    latest_term_before_quorum_nodedec dss t = latest_term_before_quorum bs t.
  Proof.
    intros Hfixed.
    rewrite /latest_term_before_quorum_nodedec /latest_term_before_quorum.
    rewrite /latest_term_before_quorum_with.
    f_equal.
    apply map_eq.
    intros x.
    rewrite 2!lookup_fmap.
    specialize (Hfixed x).
    inversion Hfixed as [ds ps Hfixed' Heq1 Heq2 | ]; [ simpl | done ].
    f_equal.
    destruct Hfixed' as [Hfixed' Hlen].
    by apply fixed_proposals_latest_term_before_nodedec.
  Qed.

  Definition ledger_in_term_nodedec t (ds : list nodedec) :=
    ledger_in_term_with (mbind nodedec_to_ledger) t ds.

  Lemma fixed_proposals_ledger_in_term_nodedec ds psa t :
    (t < length ds)%nat ->
    fixed_proposals ds psa ->
    ledger_in_term_nodedec t ds = ledger_in_term t psa.
  Proof.
    intros Hlen Hfixed.
    rewrite /ledger_in_term_nodedec /ledger_in_term /ledger_in_term_with /=.
    apply list_lookup_lt in Hlen as [d Hd].
    specialize (Hfixed _ _ Hd).
    by rewrite Hd Hfixed.
  Qed.

  Definition longest_proposal_in_term_nodedec (dss : gmap u64 (list nodedec)) t :=
    longest_proposal_in_term_with (mbind nodedec_to_ledger) dss t.

  Lemma longest_proposal_in_term_nodedec_unfold dss t :
    longest_proposal_in_term_nodedec dss t =
    longest_proposal_in_term_with (mbind nodedec_to_ledger) dss t.
  Proof. done. Qed.

  Lemma longest_proposal_in_term_nodedec_prefixes dss dsslb t :
    map_Forall2 (λ _ dslb ds, prefix dslb ds ∧ (t < length dslb)%nat) dsslb dss ->
    longest_proposal_in_term_nodedec dsslb t = longest_proposal_in_term_nodedec dss t.
  Proof.
    intros Hprefixes.
    rewrite /longest_proposal_in_term_nodedec /longest_proposal_in_term_with.
    f_equal.
    apply map_eq.
    intros nid.
    rewrite 2!lookup_fmap.
    specialize (Hprefixes nid).
    rewrite /ledger_in_term_with.
    inversion Hprefixes as [dslb ds Hprefix Heq1 Heq2|]; [ simpl | done ].
    f_equal.
    destruct Hprefix as [Hprefix Hlen].
    by rewrite (prefix_lookup_lt _ _ _ Hlen Hprefix).
  Qed.

  Lemma fixed_proposals_longest_proposal_in_term_nodedec dss (bs : gmap u64 proposals) t :
    map_Forall2 (λ _ ds psa, fixed_proposals ds psa ∧ (t < length ds)%nat) dss bs ->
    longest_proposal_in_term_nodedec dss t = longest_proposal_in_term bs t.
  Proof.
    intros Hfixed.
    rewrite /longest_proposal_in_term_nodedec /longest_proposal_in_term.
    rewrite /longest_proposal_in_term_with.
    f_equal.
    apply map_eq.
    intros x.
    rewrite 2!lookup_fmap.
    specialize (Hfixed x).
    inversion Hfixed as [ds ps Hfixed' Heq1 Heq2 | ]; [ simpl | done ].
    f_equal.
    destruct Hfixed' as [Hfixed' Hlen].
    by apply fixed_proposals_ledger_in_term_nodedec.
  Qed.

  Lemma fixed_proposals_equal_latest_longest_proposal_nodedec dss bs t v :
    map_Forall2 (λ _ ds psa, fixed_proposals ds psa ∧ (t ≤ length ds)%nat) dss bs ->
    equal_latest_longest_proposal_nodedec dss t v ->
    equal_latest_longest_proposal bs t v.
  Proof.
    rewrite /equal_latest_longest_proposal /equal_latest_longest_proposal_nodedec.
    rewrite /equal_latest_longest_proposal_with.
    intros Hfixed Heq.
    case_decide as Hv; first done.
    rewrite -Heq -latest_term_before_quorum_nodedec_unfold.
    rewrite (fixed_proposals_latest_term_before_quorum_nodedec _ _ _ Hfixed).
    set t' := latest_term_before_quorum _ _.
    rewrite -longest_proposal_in_term_nodedec_unfold.
    unshelve erewrite (fixed_proposals_longest_proposal_in_term_nodedec dss bs t' _).
    { intros nid.
      specialize (Hfixed nid).
      inversion Hfixed as [ds ps Hfixed' Heq1 Heq2|]; [ simpl | constructor ].
      constructor.
      destruct Hfixed' as [Hfixed' Hlen].
      split; first done.
      subst t'.
      eapply Nat.lt_le_trans; last apply Hlen.
      by apply latest_term_before_quorum_with_lt.
    }
    done.
  Qed.

  Definition length_of_longest_ledger (vs : gmap u64 ledger) :=
    map_fold (λ _ cur prev, (cur `max` prev)%nat) O (fmap length vs).

  Lemma length_of_longest_ledger_unfold vs :
    length_of_longest_ledger vs = map_fold (λ _ cur prev, (cur `max` prev)%nat) O (fmap length vs).
  Proof. done. Qed.

  Lemma length_of_longest_ledger_spec vs nid v :
    vs !! nid = Some v ->
    (length v ≤ length_of_longest_ledger vs)%nat.
  Proof.
    intros Hv.
    induction vs as [| nidx v' vs Hnone Hfold IH] using map_first_key_ind.
    { done. }
    rewrite /length_of_longest_ledger.
    rewrite fmap_insert map_fold_insert_first_key; last first.
    { by rewrite -fmap_insert map_first_key_fmap. }
    { by rewrite lookup_fmap Hnone. }
    destruct (decide (nidx = nid)) as [-> | Hne].
    { rewrite lookup_insert_eq in Hv. inv Hv. lia. }
    rewrite lookup_insert_ne in Hv; last done.
    specialize (IH Hv).
    rewrite /length_of_longest_ledger in IH.
    lia.
  Qed.

  Definition length_of_longest_ledger_in_term (dss : gmap u64 (list nodedec)) t :=
    let vs := omap (ledger_in_term_with (mbind nodedec_to_ledger) t) dss in
    length_of_longest_ledger vs.

  Lemma length_of_longest_ledger_in_term_spec dss nid ds t v :
    dss !! nid = Some ds ->
    ds !! t = Some (Accept v) ->
    (length v ≤ length_of_longest_ledger_in_term dss t)%nat.
  Proof.
    intros Hds Hv.
    rewrite /length_of_longest_ledger_in_term.
    apply (length_of_longest_ledger_spec _ nid).
    rewrite lookup_omap_Some.
    exists ds.
    by rewrite /ledger_in_term_with Hv.
  Qed.

  Lemma length_of_longest_ledger_in_term_singleton nid ds t v :
    ds !! t = Some (Accept v) ->
    length_of_longest_ledger_in_term {[nid := ds]} t = length v.
  Proof.
    intros Hv.
    rewrite /length_of_longest_ledger_in_term omap_singleton /ledger_in_term_with Hv /=.
    rewrite /length_of_longest_ledger map_fmap_singleton map_fold_singleton.
    lia.
  Qed.

  Lemma length_of_longest_ledger_in_term_insert_None dss nid ds t :
    dss !! nid = None ->
    mbind nodedec_to_ledger (ds !! t) = None ->
    length_of_longest_ledger_in_term (<[nid := ds]> dss) t =
    length_of_longest_ledger_in_term dss t.
  Proof.
    intros Hnid Hnone.
    rewrite /length_of_longest_ledger_in_term omap_insert.
    rewrite /ledger_in_term_with Hnone.
    by rewrite -omap_delete delete_id.
  Qed.

  Lemma length_of_longest_ledger_in_term_insert_Some_length_le dss nid ds t v :
    dss !! nid = None ->
    mbind nodedec_to_ledger (ds !! t) = Some v ->
    (length v ≤ length_of_longest_ledger_in_term dss t)%nat ->
    length_of_longest_ledger_in_term (<[nid := ds]> dss) t =
    length_of_longest_ledger_in_term dss t.
  Proof.
    intros Hnid Hv Hlen.
    rewrite /length_of_longest_ledger_in_term omap_insert.
    rewrite /ledger_in_term_with Hv {1}/length_of_longest_ledger.
    rewrite fmap_insert map_fold_insert_L; last first.
    { by rewrite lookup_fmap lookup_omap Hnid. }
    { intros x1 x2 y1 y2 y _ _ _. lia. }
    rewrite -length_of_longest_ledger_unfold.
    rewrite /length_of_longest_ledger_in_term /ledger_in_term_with in Hlen.
    lia.
  Qed.

  Lemma length_of_longest_ledger_in_term_insert_Some_length_ge dss nid ds t v :
    dss !! nid = None ->
    mbind nodedec_to_ledger (ds !! t) = Some v ->
    (length_of_longest_ledger_in_term dss t ≤ length v)%nat ->
    length_of_longest_ledger_in_term (<[nid := ds]> dss) t = length v.
  Proof.
    intros Hnid Hv Hlen.
    rewrite /length_of_longest_ledger_in_term omap_insert.
    rewrite /ledger_in_term_with Hv {1}/length_of_longest_ledger.
    rewrite fmap_insert map_fold_insert_L; last first.
    { by rewrite lookup_fmap lookup_omap Hnid. }
    { intros x1 x2 y1 y2 y _ _ _. lia. }
    rewrite -length_of_longest_ledger_unfold.
    rewrite /length_of_longest_ledger_in_term /ledger_in_term_with in Hlen.
    lia.
  Qed.

  Definition votes_in γ nids t p v : iProp Σ :=
    ∃ dss,
      "#Hdss"      ∷ ([∗ map] nid ↦ ds ∈ dss, is_past_nodedecs_lb γ nid ds) ∗
      "%Hlendss"   ∷ ⌜map_Forall (λ _ ds, length ds = t) dss⌝ ∗
      "%Hlatestq"  ∷ ⌜latest_term_before_quorum_nodedec dss t = p⌝ ∗
      "%Hlongestq" ∷ ⌜length_of_longest_ledger_in_term dss p = length v⌝ ∗
      "%Hvlatest"  ∷ ⌜map_Exists (λ _ ds, ds !! p = Some (Accept v)) dss⌝ ∗
      "%Hdomdss"   ∷ ⌜nids = dom dss⌝.

  Definition safe_base_proposal_by_length γ nids t v : iProp Σ :=
    ∃ nidsq p,
      "#Hvotes"  ∷ votes_in γ nidsq t p v ∗
      "%Hquorum" ∷ ⌜cquorum nids nidsq⌝.

  Definition past_nodedecs_latest_before γ nid termc terml v : iProp Σ :=
    ∃ ds,
      "#Hpastd"  ∷ is_past_nodedecs_lb γ nid ds ∗
      "%Hlends"  ∷ ⌜length ds = termc⌝ ∗
      "%Hlatest" ∷ ⌜latest_term_nodedec ds = terml⌝ ∗
      "%Hacpt"   ∷ ⌜ds !! terml = Some (Accept v)⌝.

  Definition proposed_cmds γ v : iProp Σ := [∗ list] c ∈ v, is_cmd_receipt γ c.

  Definition paxos_inv γ nids : iProp Σ :=
    ∃ log cpool ps psb termlm,
      (* external states *)
      "Hlog"   ∷ own_log_half γ log ∗
      "Hcpool" ∷ own_cpool_half γ cpool ∗
      (* internal states *)
      "Hps"  ∷ own_proposals γ ps ∗
      "Hpsb" ∷ own_base_proposals γ psb ∗
      (* node states *)
      "Hnodes" ∷ ([∗ map] nid ↦ terml ∈ termlm, node_inv γ nids nid terml) ∗
      (* constraints between internal and external states *)
      "#Hsafelog" ∷ safe_ledger γ nids log ∗
      "#Hsubsume" ∷ ([∗ map] t ↦ v ∈ ps, proposed_cmds γ v) ∗
      (* constraints on internal states *)
      "#Hsafepsb"   ∷ ([∗ map] t ↦ v ∈ psb, safe_base_proposal γ nids t v) ∗
      "%Hvp"        ∷ ⌜valid_proposals ps psb⌝ ∗
      "%Hdomtermlm" ∷ ⌜dom termlm = nids⌝ ∗
      "%Hdompsb"    ∷ ⌜free_terms (dom psb) termlm⌝ ∗
      (* constraint on the external states *)
      "%Hcsincl"    ∷ ⌜cpool_subsume_log log cpool⌝.

  #[global]
  Instance paxos_inv_timeless γ nids :
    Timeless (paxos_inv γ nids).
  Proof. apply _. Defined.

  Definition paxoscoreNS := paxosNS .@ "core".

  Definition know_paxos_inv γ nids : iProp Σ :=
    inv paxoscoreNS (paxos_inv γ nids).

End inv.

Section inv_file.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Definition paxosfileNS := paxosNS .@ "file".
  (* TODO: make name consistent, also think about the right NS structure *)
  Definition pxcrashNS := nroot .@ "pxcrash".

  (* TODO: using nat (rather than u64) here would be more consistent with the
  principle that in the protocol world types are perfect. *)
  Inductive pxdur :=
  | PaxosDurable (termc terml : u64) (log : list byte_string) (lsn : u64).

  Definition own_paxos_durable
    γ (nidme : u64) (dst : pxdur) : iProp Σ :=
    match dst with
    | PaxosDurable termc terml log lsnc =>
        "Htermc" ∷ own_current_term_half γ nidme (uint.nat termc) ∗
        "Hterml" ∷ own_ledger_term_half γ nidme (uint.nat terml) ∗
        "Hlogn"  ∷ own_node_ledger_half γ nidme log ∗
        "Hlsnc"  ∷ own_committed_lsn_half γ nidme (uint.nat lsnc)
    end.

  (* Required during recovery. *)
  Definition valid_wal_entry (cmd : pxcmd) :=
    match cmd with
    | CmdPaxosPrepare term => Z.of_nat term < 2 ^ 64
    | CmdPaxosAdvance term lsn _ => Z.of_nat term < 2 ^ 64 ∧ Z.of_nat lsn < 2 ^ 64
    | CmdPaxosAccept lsn _ => Z.of_nat lsn < 2 ^ 64
    | CmdPaxosExpand lsn => Z.of_nat lsn < 2 ^ 64
    | _ => True
    end.

  Definition node_file_inv (γ : paxos_names) (nid : u64) : iProp Σ :=
    ∃ (wal : list pxcmd) (fname : byte_string) (content : list u8),
      "Hwalfile"   ∷ own_node_wal_half γ nid wal ∗
      "Hfile"      ∷ fname f↦ content ∗
      "#Hwalfname" ∷ is_node_wal_fname γ nid fname ∗
      "%Hvdwal"    ∷ ⌜Forall valid_wal_entry wal⌝ ∗
      "%Hencwal"   ∷ ⌜encode_paxos_cmds wal = content⌝.

  Definition paxos_file_inv (γ : paxos_names) (nids : gset u64) : iProp Σ :=
    [∗ set] nid ∈ nids, node_file_inv γ nid.

  #[global]
  Instance paxos_file_inv_timeless γ nids :
    Timeless (paxos_file_inv γ nids).
  Proof. apply _. Defined.

  Definition know_paxos_file_inv γ nids : iProp Σ :=
    inv paxosfileNS (paxos_file_inv γ nids).

End inv_file.

Section inv_network.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Definition paxosnetNS := paxosNS .@ "net".

  Definition safe_request_vote_req γ (term lsnlc : u64) : iProp Σ :=
    is_prepare_lsn γ (uint.nat term) (uint.nat lsnlc).

  Definition safe_append_entries_req
    γ nids (term lsnlc lsne : u64) (ents : list byte_string) : iProp Σ :=
    ∃ (logleader logcmt : list byte_string),
      "#Hpfb"       ∷ prefix_base_ledger γ (uint.nat term) logleader ∗
      "#Hpfg"       ∷ prefix_growing_ledger γ (uint.nat term) logleader ∗
      "#Hlogcmt"    ∷ safe_ledger_above γ nids (uint.nat term) logcmt ∗
      "%Hlogleader" ∷ ⌜(uint.nat lsne ≤ length logleader)%nat⌝ ∗
      "%Hents"      ∷ ⌜drop (uint.nat lsne) logleader = ents⌝ ∗
      "%Hlogcmt"    ∷ ⌜length logcmt = uint.nat lsnlc⌝.

  Definition safe_pxreq γ nids req : iProp Σ :=
    match req with
    | RequestVoteReq term lsnlc => safe_request_vote_req γ term lsnlc
    | AppendEntriesReq term lsnlc lsne ents =>
        safe_append_entries_req γ nids term lsnlc lsne ents
    end.

  #[global]
  Instance safe_pxreq_persistent γ nids req :
    Persistent (safe_pxreq γ nids req).
  Proof. destruct req; apply _. Defined.

  #[global]
  Instance safe_pxreq_timeless γ nids req :
    Timeless (safe_pxreq γ nids req).
  Proof. destruct req; apply _. Defined.

  Definition safe_request_vote_resp
    γ (nids : gset u64) (nid term terme : u64) (ents : list byte_string) : iProp Σ :=
    ∃ (logpeer : list byte_string) (lsne : u64),
      "#Hpromise" ∷ past_nodedecs_latest_before γ nid (uint.nat term) (uint.nat terme) logpeer ∗
      "#Hlsne"    ∷ is_prepare_lsn γ (uint.nat term) (uint.nat lsne) ∗
      "%Hents"    ∷ ⌜drop (uint.nat lsne) logpeer = ents⌝ ∗
      "%Hinnids"  ∷ ⌜nid ∈ nids⌝.

  Definition safe_append_entries_resp
    γ (nids : gset u64) (nid term lsneq : u64) : iProp Σ :=
    ∃ (logacpt : list byte_string),
      "#Haoc"     ∷ (is_accepted_proposal_lb γ nid (uint.nat term) logacpt ∨
                     safe_ledger_above γ nids (uint.nat term) logacpt) ∗
      "%Hlogacpt" ∷ ⌜length logacpt = uint.nat lsneq⌝ ∗
      "%Hinnids"  ∷ ⌜nid ∈ nids⌝.

  Definition safe_pxresp γ nids resp : iProp Σ :=
    match resp with
    | RequestVoteResp nid term terme ents =>
        safe_request_vote_resp γ nids nid term terme ents
    | AppendEntriesResp nid term lsneq =>
        safe_append_entries_resp γ nids nid term lsneq
    end.

  #[global]
  Instance safe_pxresp_persistent γ nids resp :
    Persistent (safe_pxresp γ nids resp).
  Proof. destruct resp; apply _. Defined.

  #[global]
  Instance safe_pxresp_timeless γ nids resp :
    Timeless (safe_pxresp γ nids resp).
  Proof. destruct resp; apply _. Defined.

  Definition listen_inv
    (addr : chan) (ms : gset message) nids γ : iProp Σ :=
    ∃ (reqs : gset pxreq),
      "Hms"      ∷ addr c↦ ms ∗
      (* senders are always reachable *)
      "#Hsender" ∷ ([∗ set] trml ∈ set_map msg_sender ms, is_terminal γ trml) ∗
      "#Hreqs"   ∷ ([∗ set] req ∈ reqs, safe_pxreq γ nids req) ∗
      "%Henc"    ∷ ⌜(set_map msg_data ms : gset (list u8)) ⊆ set_map encode_pxreq reqs⌝.

  Definition connect_inv (trml : chan) (ms : gset message) nids γ : iProp Σ :=
    ∃ (resps : gset pxresp),
      "Hms"     ∷ trml c↦ ms ∗
      "#Hresps" ∷ ([∗ set] resp ∈ resps, safe_pxresp γ nids resp) ∗
      "%Henc"   ∷ ⌜(set_map msg_data ms : gset (list u8)) ⊆ set_map encode_pxresp resps⌝.

  Definition paxos_network_inv
    (γ : paxos_names) (addrm : gmap u64 chan) : iProp Σ :=
    ∃ (listens : gmap chan (gset message)) (connects : gmap chan (gset message)),
      "Hlistens"   ∷ ([∗ map] a ↦ ms ∈ listens, listen_inv a ms (dom addrm) γ) ∗
      "Hconnects"  ∷ ([∗ map] t ↦ ms ∈ connects, connect_inv t ms (dom addrm) γ) ∗
      "Hterminals" ∷ own_terminals γ (dom connects) ∗
      "%Himgaddrm" ∷ ⌜map_img addrm = dom listens⌝.

  #[global]
  Instance paxos_network_inv_timeless γ addrm :
    Timeless (paxos_network_inv γ addrm).
  Proof. apply _. Defined.

  Definition know_paxos_network_inv γ addrm : iProp Σ :=
    inv paxosnetNS (paxos_network_inv γ addrm).

End inv_network.

Section lemma.
  Context `{!paxos_ghostG Σ}.

  Lemma paxos_inv_impl_cpool_subsume_log γ nids log cpool :
    own_log_half γ log -∗
    own_cpool_half γ cpool -∗
    paxos_inv γ nids -∗
    ⌜cpool_subsume_log log cpool⌝.
  Proof.
    iIntros "HlogX HcpoolX Hinv".
    iNamed "Hinv".
    iDestruct (log_agree with "Hlog HlogX") as %->.
    iDestruct (cpool_agree with "Hcpool HcpoolX") as %->.
    done.
  Qed.

  Lemma equal_latest_longest_proposal_nodedec_prefix dss dsslb t v :
    map_Forall2 (λ _ dslb ds, prefix dslb ds ∧ (t ≤ length dslb)%nat) dsslb dss ->
    equal_latest_longest_proposal_nodedec dsslb t v ->
    equal_latest_longest_proposal_nodedec dss t v.
  Proof.
    rewrite /equal_latest_longest_proposal_nodedec /equal_latest_longest_proposal_with.
    rewrite -2!latest_term_before_quorum_nodedec_unfold.
    rewrite -2!longest_proposal_in_term_nodedec_unfold.
    intros Hprefixes Heq.
    case_decide as Ht; first done.
    rewrite -(latest_term_before_quorum_nodedec_prefixes _ _ _ Hprefixes).
    set t' := (latest_term_before_quorum_nodedec _ _) in Heq *.
    assert (Hlt : (t' < t)%nat).
    { by apply latest_term_before_quorum_with_lt. }
    rewrite -(longest_proposal_in_term_nodedec_prefixes dss dsslb); first apply Heq.
    apply (map_Forall2_impl _ _ _ _ Hprefixes).
    intros _ dslb ds [Hprefix Hlen].
    split; [done | lia].
  Qed.

  Lemma nodes_inv_is_accepted_proposal_lb_impl_prefix γ bs nid1 nid2 t v1 v2 :
    nid1 ∈ dom bs ->
    nid2 ∈ dom bs ->
    is_accepted_proposal_lb γ nid1 t v1 -∗
    is_accepted_proposal_lb γ nid2 t v2 -∗
    ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa) -∗
    ⌜prefix v1 v2 ∨ prefix v2 v1⌝.
  Proof.
    iIntros (Hnid1 Hnid2) "Hv1 Hv2 Hnodes".
    iAssert (prefix_growing_ledger γ t v1)%I as "#Hvub1".
    { rewrite elem_of_dom in Hnid1.
      destruct Hnid1 as [ps Hps].
      iDestruct (big_sepM_lookup _ _ nid1 with "Hnodes") as "Hnode"; first apply Hps.
      iNamed "Hnode".
      iDestruct (accepted_proposal_lb_lookup with "Hv1 Hpsa") as %(vub & Hvub & Hprefix).
      iDestruct (big_sepM_lookup with "Hpsaubs") as (vub') "[Hvub' %Hprefix']"; first apply Hvub.
      iExists vub'.
      iFrame "Hvub'".
      iPureIntro.
      by trans vub.
    }
    iAssert (prefix_growing_ledger γ t v2)%I as "#Hvub2".
    { rewrite elem_of_dom in Hnid2.
      destruct Hnid2 as [ps Hps].
      iDestruct (big_sepM_lookup _ _ nid2 with "Hnodes") as "Hnode"; first apply Hps.
      iNamed "Hnode".
      iDestruct (accepted_proposal_lb_lookup with "Hv2 Hpsa") as %(vub & Hvub & Hprefix).
      iDestruct (big_sepM_lookup with "Hpsaubs") as (vub') "[Hvub' %Hprefix']"; first apply Hvub.
      iExists vub'.
      iFrame "Hvub'".
      iPureIntro.
      by trans vub.
    }
    iDestruct "Hvub1" as (vub1) "[#Hvub1 %Hprefix1]".
    iDestruct "Hvub2" as (vub2) "[#Hvub2 %Hprefix2]".
    iDestruct (proposal_lb_prefix with "Hvub1 Hvub2") as %Hprefix.
    iPureIntro.
    destruct Hprefix as [Hprefix | Hprefix].
    { apply (prefix_common_ub _ _ vub2); last apply Hprefix2.
      by trans vub1.
    }
    { apply (prefix_common_ub _ _ vub1); first apply Hprefix1.
      by trans vub2.
    }
  Qed.

  Lemma nodes_inv_impl_valid_base_proposals γ nids bs psb dss :
    dom bs = nids ->
    ([∗ map] t ↦ v ∈ psb, safe_base_proposal γ nids t v) -∗
    ([∗ map] nid ↦ ds; psa ∈ dss; bs, node_inv_ds_psa γ nid ds psa) -∗
    ⌜valid_base_proposals bs psb⌝.
  Proof.
    iIntros (Hdombs) "Hsafe Hinv".
    iIntros (t v Hv).
    iDestruct (big_sepM_lookup with "Hsafe") as "Hsafe"; first apply Hv.
    iNamed "Hsafe".
    rewrite /valid_base_proposal.
    rewrite big_sepM2_alt.
    iDestruct "Hinv" as "[%Hdomdss Hinv]".
    iDestruct (big_sepM_dom_subseteq_difference _ _ (dom dssqlb) with "Hinv") as "Hm".
    { rewrite dom_map_zip_with_L Hdomdss intersection_idemp Hdombs.
      by destruct Hquorum as [Hincl _].
    }
    iDestruct "Hm" as (m [Hdomm Hinclm]) "[Hm _]".
    set dssq := fst <$> m.
    set bsq := snd <$> m.
    iExists bsq.
    iAssert (⌜map_Forall2 (λ _ dslb ds, prefix dslb ds ∧ (t ≤ length dslb)%nat) dssqlb dssq⌝)%I
      as %Hprefix.
    { iIntros (x).
      destruct (dssqlb !! x) as [dslb |] eqn:Hdslb, (dssq !! x) as [ds |] eqn:Hds; last first.
      { eauto using None_Forall2. }
      { rewrite -not_elem_of_dom -Hdomm not_elem_of_dom in Hdslb.
        subst dssq.
        by rewrite lookup_fmap Hdslb /= in Hds.
      }
      { subst dssq.
        by rewrite -not_elem_of_dom dom_fmap_L Hdomm not_elem_of_dom Hdslb in Hds.
      }
      simpl.
      iDestruct (big_sepM_lookup with "Hdsq") as "Hdsqx"; first apply Hdslb.
      rewrite lookup_fmap_Some in Hds.
      destruct Hds as ([ds' psa] & Hds & Hmx). simpl in Hds. subst ds'.
      iDestruct (big_sepM_lookup with "Hm") as "Hinv"; first apply Hmx.
      iNamed "Hinv". simpl.
      iDestruct (past_nodedecs_prefix with "Hdsqx Hpastd") as %Hprefix.
      iPureIntro.
      constructor.
      split; first done.
      specialize (Hlen _ _ Hdslb). simpl in Hlen.
      lia.
    }
    pose proof (equal_latest_longest_proposal_nodedec_prefix _ _ _ _ Hprefix Heq) as Heq'.
    iAssert (⌜map_Forall2 (λ _ ds psa, fixed_proposals ds psa ∧ (t ≤ length ds)%nat) dssq bsq⌝)%I
      as %Hfixed.
    { iIntros (x).
      destruct (dssq !! x) as [ds |] eqn:Hds, (bsq !! x) as [psa |] eqn:Hpsa; last first.
      { eauto using None_Forall2. }
      { rewrite -not_elem_of_dom dom_fmap_L in Hds.
        apply elem_of_dom_2 in Hpsa.
        by rewrite dom_fmap_L in Hpsa.
      }
      { rewrite -not_elem_of_dom dom_fmap_L in Hpsa.
        apply elem_of_dom_2 in Hds.
        by rewrite dom_fmap_L in Hds.
      }
      simpl.
      iDestruct (big_sepM_lookup _ _ x (ds, psa) with "Hm") as "Hinv".
      { rewrite lookup_fmap_Some in Hds.
        destruct Hds as ([ds1 psa1] & Hds & Hmx1). simpl in Hds. subst ds1.
        rewrite lookup_fmap_Some in Hpsa.
        destruct Hpsa as ([ds2 psa2] & Hpsa & Hmx2). simpl in Hpsa. subst psa2.
        rewrite Hmx1 in Hmx2.
        by inv Hmx2.
      }
      iNamed "Hinv".
      specialize (Hprefix x).
      assert (is_Some (dssqlb !! x)) as [dslb Hdslb].
      { rewrite -elem_of_dom -Hdomm elem_of_dom.
        apply lookup_fmap_Some in Hds as (dp & _ & Hinv).
        done.
      }
      rewrite Hds Hdslb /= in Hprefix.
      iPureIntro.
      constructor; split; first apply Hfixed.
      inv Hprefix.
      pose proof (prefix_length dslb ds).
      intuition. lia.
    }
    iPureIntro.
    split.
    { subst bsq.
      trans (snd <$> map_zip dss bs).
      { by apply map_fmap_mono. }
      rewrite snd_map_zip; first done.
      intros x Hbsx.
      by rewrite -elem_of_dom -Hdomdss elem_of_dom in Hbsx.
    }
    split.
    { subst bsq.
      rewrite dom_fmap_L Hdomm Hdombs.
      by destruct Hquorum as [_ Hquorum].
    }
    by eapply fixed_proposals_equal_latest_longest_proposal_nodedec.
  Qed.

  Lemma nodes_inv_impl_valid_lb_ballots γ bs psb :
    own_base_proposals γ psb -∗
    ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa) -∗
    ⌜valid_lb_ballots bs psb⌝.
  Proof.
    iIntros "Hpsb Hinv".
    iIntros (nid psa Hpsa).
    iDestruct (big_sepM_lookup with "Hinv") as "Hinv"; first apply Hpsa.
    iNamed "Hinv".
    iIntros (t v Hv).
    iDestruct (big_sepM_lookup with "Hpsalbs") as (vlb) "[Hvlb %Hprefix]"; first apply Hv.
    iDestruct (base_proposal_lookup with "Hvlb Hpsb") as %Hvlb.
    by eauto.
  Qed.

  Lemma nodes_inv_impl_valid_ub_ballots γ bs ps :
    own_proposals γ ps -∗
    ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa) -∗
    ⌜valid_ub_ballots bs ps⌝.
  Proof.
    iIntros "Hps Hinv".
    iIntros (nid psa Hpsa).
    iDestruct (big_sepM_lookup with "Hinv") as "Hinv"; first apply Hpsa.
    iNamed "Hinv".
    iIntros (t v Hv).
    iDestruct (big_sepM_lookup with "Hpsaubs") as (vlb) "[Hvub %Hprefix]"; first apply Hv.
    iDestruct (proposals_prefix with "Hvub Hps") as %(vub & Hvub & Hprefixvlb).
    iPureIntro.
    exists vub.
    split; first apply Hvub.
    by trans vlb.
  Qed.

  Lemma paxos_inv_impl_nodes_inv γ nids :
    paxos_inv γ nids -∗
    ∃ termlm, ([∗ map] nid ↦ terml ∈ termlm, node_inv γ nids nid terml) ∗ ⌜dom termlm = nids⌝.
  Proof. iNamed 1. by iFrame. Qed.

  Lemma paxos_inv_impl_node_inv {γ nids} nid :
    nid ∈ nids ->
    paxos_inv γ nids -∗
    ∃ terml, node_inv γ nids nid terml.
  Proof.
    iIntros (Hnids) "Hinv".
    iDestruct (paxos_inv_impl_nodes_inv with "Hinv") as (termlm) "[Hnodes %Hdomtermlm]".
    assert (is_Some (termlm !! nid)) as [terml Hterml].
    { by rewrite -elem_of_dom Hdomtermlm. }
    iDestruct (big_sepM_lookup with "Hnodes") as "Hnode"; first apply Hterml.
    iFrame.
  Qed.

  Lemma node_inv_extract_ds_psa γ nids nid terml :
    node_inv γ nids nid terml -∗
    ∃ ds psa, node_inv_without_ds_psa γ nids nid terml ds psa ∗
              node_inv_ds_psa γ nid ds psa.
  Proof. iIntros "Hinv". iNamed "Hinv". iFrame "∗ # %". Qed.

  Lemma nodes_inv_extract_ds_psa γ nids termlm :
    ([∗ map] nid ↦ terml ∈ termlm, node_inv γ nids nid terml) -∗
    ∃ dss bs, ([∗ map] nid ↦ terml; dp ∈ termlm; map_zip dss bs,
                 node_inv_without_ds_psa γ nids nid terml dp.1 dp.2) ∗
              ([∗ map] nid ↦ ds; psa ∈ dss; bs, node_inv_ds_psa γ nid ds psa).
  Proof.
    iIntros "Hinvs".
    set Φ := (λ nid terml dp,
                node_inv_without_ds_psa γ nids nid terml dp.1 dp.2 ∗
                node_inv_ds_psa γ nid dp.1 dp.2)%I.
    iDestruct (big_sepM_sepM2_exists Φ termlm with "[Hinvs]") as (dpm) "Hdpm".
    { iApply (big_sepM_mono with "Hinvs").
      iIntros (nid terml Hterml) "Hinv".
      subst Φ.
      iNamed "Hinv".
      iExists (ds, psa).
      iFrame "∗ # %".
    }
    iDestruct (big_sepM2_dom with "Hdpm") as %Hdom.
    subst Φ.
    iNamed "Hdpm".
    iDestruct (big_sepM2_sep with "Hdpm") as "[Hinv Hdp]".
    iExists (fst <$> dpm), (snd <$> dpm).
    rewrite map_zip_fst_snd.
    iFrame "Hinv".
    iDestruct (big_sepM2_flip with "Hdp") as "Hdp".
    rewrite -big_sepM_big_sepM2; last apply Hdom.
    rewrite big_sepM2_alt map_zip_fst_snd.
    iFrame "Hdp".
    iPureIntro.
    by rewrite 2!dom_fmap_L.
  Qed.

  Lemma nodes_inv_merge_ds_psa γ nids termlm dss bs :
    ([∗ map] nid ↦ terml; dp ∈ termlm; map_zip dss bs,
       node_inv_without_ds_psa γ nids nid terml dp.1 dp.2) -∗
    ([∗ map] nid ↦ ds; psa ∈ dss; bs, node_inv_ds_psa γ nid ds psa) -∗
    ([∗ map] nid ↦ terml ∈ termlm, node_inv γ nids nid terml).
  Proof.
    iIntros "Hinv Hdp".
    iDestruct (big_sepM2_alt with "Hdp") as "[%Hdom Hdp]".
    iDestruct (big_sepM2_dom with "Hinv") as %Hdomtermlm.
    iDestruct (big_sepM_big_sepM2_1 with "Hdp") as "Hdp".
    { apply Hdomtermlm. }
    rewrite big_sepM2_flip.
    iCombine "Hinv Hdp" as "Hinv".
    rewrite -big_sepM2_sep.
    iApply (big_sepM2_sepM_impl with "Hinv").
    { apply Hdomtermlm. }
    iIntros (nid dp terml terml' Hdp Hterml Hterml') "!> [Hinv Hdp]".
    rewrite Hterml in Hterml'. symmetry in Hterml'. inv Hterml'.
    iNamed "Hinv".
    iNamed "Hdp".
    iNamed "Hpsa".
    iFrame "∗ # %".
  Qed.

  Lemma nodes_inv_ds_psa_impl_nodes_inv_psa γ dss bs :
    ([∗ map] nid ↦ ds; psa ∈ dss; bs, node_inv_ds_psa γ nid ds psa) -∗
    ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa).
  Proof.
    iIntros "Hpds".
    rewrite big_sepM2_flip.
    iApply (big_sepM2_sepM_impl with "Hpds"); first done.
    iIntros (nid psa ds psa' Hpsa Hds Hpsa') "!> Hpd".
    rewrite Hpsa in Hpsa'. symmetry in Hpsa'. inv Hpsa'.
    by iNamed "Hpd".
  Qed.

  Lemma nodes_inv_impl_nodes_inv_psa γ nids termlm :
    ([∗ map] nid ↦ terml ∈ termlm, node_inv γ nids nid terml) -∗
    ∃ bs, ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa) ∗ ⌜dom bs = dom termlm⌝.
  Proof.
    iIntros "Hnodes".
    iDestruct (nodes_inv_extract_ds_psa with "Hnodes") as (dss bs) "[Hxdp Hdp]".
    iDestruct (big_sepM2_dom with "Hxdp") as %Hdom.
    iDestruct (big_sepM2_dom with "Hdp") as %Hdom'.
    rewrite dom_map_zip_with_L Hdom' intersection_idemp_L in Hdom.
    iDestruct (nodes_inv_ds_psa_impl_nodes_inv_psa with "Hdp") as "Hp".
    iExists bs.
    by iFrame.
  Qed.

  Lemma paxos_inv_impl_nodes_inv_psa γ nids :
    paxos_inv γ nids -∗
    ∃ bs, ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa) ∗ ⌜dom bs = nids⌝.
  Proof.
    iNamed 1.
    rewrite -Hdomtermlm.
    iApply (nodes_inv_impl_nodes_inv_psa with "Hnodes").
  Qed.

  Lemma nodes_inv_safe_ledger_in_impl_chosen_in γ nids bs t v :
    dom bs = nids ->
    safe_ledger_in γ nids t v -∗
    ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa) -∗
    ⌜chosen_in bs t v⌝.
  Proof.
    iIntros (Hdombs) "#Hsafe Hinv".
    iNamed "Hsafe".
    set bsq := (filter (λ x, x.1 ∈ nidsq) bs).
    iExists bsq.
    rewrite base.and_assoc.
    iSplit.
    { iPureIntro.
      split; first apply map_filter_subseteq.
      rewrite Hdombs.
      subst bsq.
      destruct Hquorum as [Hincl Hquorum].
      rewrite (dom_filter_L _ _ nidsq); first apply Hquorum.
      intros nidx.
      split; last by intros (ps & _ & Hin).
      intros Hin.
      assert (is_Some (bs !! nidx)) as [ps Hps].
      { rewrite -elem_of_dom Hdombs. set_solver. }
      by exists ps.
    }
    iIntros (nid' ps Hps).
    iDestruct (big_sepS_elem_of _ _ nid' with "Hacpt") as "Hvacpt'".
    { by apply map_lookup_filter_Some_1_2 in Hps. }
    iDestruct "Hvacpt'" as (v') "[Hvacpt' %Hlen]".
    iDestruct (nodes_inv_is_accepted_proposal_lb_impl_prefix with "Hvacpt Hvacpt' Hinv") as %Hprefix.
    { by rewrite -Hdombs in Hmember. }
    { apply elem_of_dom_2 in Hps.
      apply (elem_of_weaken _ (dom bsq)); first done.
      apply dom_filter_subseteq.
    }
    assert (Hvv' : prefix v v').
    { destruct Hprefix as [Hprefix | Hprefix]; first apply Hprefix.
      by rewrite (prefix_length_eq _ _ Hprefix Hlen).
    }
    iDestruct (accepted_proposal_lb_weaken v with "Hvacpt'") as "Hlb"; first apply Hvv'.
    iDestruct (big_sepM_lookup with "Hinv") as "Hnode".
    { eapply lookup_weaken; [apply Hps | apply map_filter_subseteq]. }
    iNamed "Hnode".
    iDestruct (accepted_proposal_prefix with "Hvacpt' Hpsa") as %(va & Hva & Hprefixva).
    iPureIntro.
    exists va.
    split; first apply Hva.
    by trans v'.
  Qed.

  Lemma accepted_proposal_past_nodedecs_impl_prefix γ dss bs nid1 nid2 dslb t v1 v2 :
    nid1 ∈ dom bs ->
    nid2 ∈ dom bs ->
    dslb !! t = Some (Accept v2) ->
    is_accepted_proposal_lb γ nid1 t v1 -∗
    is_past_nodedecs_lb γ nid2 dslb -∗
    ([∗ map] nid ↦ ds; psa ∈ dss; bs, node_inv_ds_psa γ nid ds psa) -∗
    ⌜prefix v1 v2 ∨ prefix v2 v1⌝.
  Proof.
    iIntros (Hnid1 Hnid2 Hv2) "Hv1 Hdslb Hnodes".
    iAssert (prefix_growing_ledger γ t v1)%I as "#Hvub1".
    { rewrite elem_of_dom in Hnid1.
      destruct Hnid1 as [ps Hps].
      iDestruct (nodes_inv_ds_psa_impl_nodes_inv_psa with "Hnodes") as "Hnodes".
      iDestruct (big_sepM_lookup _ _ nid1 with "Hnodes") as "Hnode"; first apply Hps.
      iNamed "Hnode".
      iDestruct (accepted_proposal_lb_lookup with "Hv1 Hpsa") as %(vub & Hvub & Hprefix).
      iDestruct (big_sepM_lookup with "Hpsaubs") as (vub') "[Hvub' %Hprefix']"; first apply Hvub.
      iExists vub'.
      iFrame "Hvub'".
      iPureIntro.
      by trans vub.
    }
    iDestruct (big_sepM2_dom with "Hnodes") as %Hdom.
    assert (is_Some (dss !! nid2)) as [ds Hds].
    { by rewrite -elem_of_dom Hdom. }
    assert (is_Some (bs !! nid2)) as [psa Hpsa].
    { by rewrite -elem_of_dom. }
    iDestruct (big_sepM2_lookup with "Hnodes") as "Hnode"; [apply Hds | apply Hpsa |].
    iNamed "Hnode".
    iDestruct (past_nodedecs_prefix with "Hdslb Hpastd") as %Hprefix.
    pose proof (prefix_lookup_Some _ _ _ _ Hv2 Hprefix) as Hdst.
    specialize (Hfixed _ _ Hdst). simpl in Hfixed.
    iNamed "Hpsa".
    iDestruct (big_sepM_lookup with "Hpsaubs") as "#Hvub2".
    { apply Hfixed. }
    iApply (prefix_growing_ledger_impl_prefix with "Hvub1 Hvub2").
  Qed.

  Lemma nodes_inv_safe_ledger_impl_chosen γ nids bs v :
    dom bs = nids ->
    safe_ledger γ nids v -∗
    ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa) -∗
    ⌜chosen bs v⌝.
  Proof.
    iIntros (Hdombs) "[%t #Hsafe] Hinv".
    iExists t.
    by iApply (nodes_inv_safe_ledger_in_impl_chosen_in with "Hsafe Hinv").
  Qed.

  Lemma safe_ledger_prefix_base_ledger_impl_prefix γ nids t1 t2 v1 v2 :
    (t1 < t2)%nat ->
    safe_ledger_in γ nids t1 v1 -∗
    prefix_base_ledger γ t2 v2 -∗
    paxos_inv γ nids -∗
    ⌜prefix v1 v2⌝.
  Proof.
    iIntros (Hlt) "Hsafev1 Hpfb Hinv".
    iNamed "Hinv".
    iDestruct (nodes_inv_extract_ds_psa with "Hnodes") as (dss bs) "[Hndp Hnodes]".
    (* Obtain [dom termlm = dom bs]. *)
    iDestruct (big_sepM2_dom with "Hnodes") as %Hdomdp.
    iDestruct (big_sepM2_dom with "Hndp") as %Hdom.
    rewrite dom_map_zip_with_L Hdomdp intersection_idemp_L Hdomtermlm in Hdom.
    symmetry in Hdom.
    iClear "Hndp".
    (* Obtain [valid_base_proposals], [valid_lb_ballots], and [valid_ub_ballots]. *)
    iDestruct (nodes_inv_impl_valid_base_proposals with "Hsafepsb Hnodes") as %Hvbp.
    { apply Hdom. }
    iDestruct (nodes_inv_ds_psa_impl_nodes_inv_psa with "Hnodes") as "Hnodes".
    iDestruct (nodes_inv_impl_valid_lb_ballots with "Hpsb Hnodes") as %Hvlb.
    iDestruct (nodes_inv_impl_valid_ub_ballots with "Hps Hnodes") as %Hvub.
    (* Obtain [proposed_after_chosen] from the above. *)
    pose proof (vlb_vub_vbp_impl_pac _ _ _ Hvlb Hvub Hvbp) as Hpac.
    (* Obtain [chosen_in bs p v1] *)
    iDestruct (nodes_inv_safe_ledger_in_impl_chosen_in with "Hsafev1 Hnodes") as %Hchosen.
    { apply Hdom. }
    iDestruct "Hpfb" as (vb) "[Hvb %Hprefix]".
    (* Obtain [psb !! t2 = Some vb]. *)
    iDestruct (base_proposal_lookup with "Hvb Hpsb") as %Hvb.
    iPureIntro.
    specialize (Hpac _ _ _ _ Hlt Hchosen Hvb).
    by trans vb.
  Qed.

  Lemma node_inv_past_nodedecs_impl_prefix_base_ledger γ nid ds dslb psa t v :
    dslb !! t = Some (Accept v) ->
    is_past_nodedecs_lb γ nid dslb -∗
    node_inv_ds_psa γ nid ds psa -∗
    prefix_base_ledger γ t v.
  Proof.
    iIntros (Hv) "Hdslb Hnode".
    iNamed "Hnode". iNamed "Hpsa".
    iDestruct (past_nodedecs_prefix with "Hdslb Hpastd") as %Hprefix.
    pose proof (prefix_lookup_Some _ _ _ _ Hv Hprefix) as Hdst.
    specialize (Hfixed _ _ Hdst).
    by iDestruct (big_sepM_lookup with "Hpsalbs") as "?"; first apply Hfixed.
  Qed.

  Lemma safe_ledger_past_nodedecs_impl_prefix γ nids nid dslb t1 t2 v1 v2 :
    nid ∈ nids ->
    (t1 < t2)%nat ->
    dslb !! t2 = Some (Accept v2) ->
    safe_ledger_in γ nids t1 v1 -∗
    is_past_nodedecs_lb γ nid dslb -∗
    paxos_inv γ nids -∗
    ⌜prefix v1 v2⌝.
  Proof.
    iIntros (Hnid Hlt Hv2) "Hsafe Hdslb Hinv".    
    (* Obtain [prefix_base_ledger γ t2 v2]. *)
    iAssert (prefix_base_ledger γ t2 v2)%I as "#Hpfb".
    { iNamed "Hinv".
      iDestruct (nodes_inv_extract_ds_psa with "Hnodes") as (dss bs) "[Hndp Hnodes]".
      (* Obtain [dom termlm = dom bs]. *)
      iDestruct (big_sepM2_dom with "Hnodes") as %Hdomdp.
      iDestruct (big_sepM2_dom with "Hndp") as %Hdom.
      rewrite dom_map_zip_with_L Hdomdp intersection_idemp_L Hdomtermlm in Hdom.
      symmetry in Hdom.
      iClear "Hndp".
      assert (is_Some (dss !! nid)) as [ds Hds].
      { by rewrite -elem_of_dom Hdomdp Hdom. }
      assert (is_Some (bs !! nid)) as [psa Hpsa].
      { by rewrite -elem_of_dom Hdom. }
      iDestruct (big_sepM2_lookup with "Hnodes") as "Hnode"; [apply Hds | apply Hpsa |].
      by iApply (node_inv_past_nodedecs_impl_prefix_base_ledger with "Hdslb Hnode").
    }
    by iApply (safe_ledger_prefix_base_ledger_impl_prefix with "Hsafe Hpfb Hinv").
  Qed.

  Lemma accepted_proposal_growing_proposal_impl_prefix γ nids nid t v1 v2 :
    nid ∈ nids ->
    is_accepted_proposal_lb γ nid t v1 -∗
    own_proposal γ t v2 -∗
    paxos_inv γ nids -∗
    ⌜prefix v1 v2⌝.
  Proof.
    iIntros (Hinnids) "Hv1 Hv2 Hinv".
    iNamed "Hinv".
    rewrite -Hdomtermlm elem_of_dom in Hinnids.
    destruct Hinnids as [terml Hterml].
    iDestruct (big_sepM_lookup with "Hnodes") as "Hnode"; first apply Hterml.
    iNamed "Hnode".
    iDestruct (accepted_proposal_prefix with "Hv1 Hpsa") as %(vub1 & Hvub1 & Hprefix1).
    iDestruct (big_sepM_lookup with "Hpsaubs") as (vub2) "[Hvub2 %Hprefix2]"; first apply Hvub1.
    iDestruct (proposal_prefix with "Hvub2 Hv2") as %Hprefix.
    iPureIntro.
    trans vub1; first done.
    by trans vub2.
  Qed.

  Lemma free_terms_after_latest_term_before psa t1 t2 :
    (t1 < t2)%nat ->
    is_Some (psa !! t1) ->
    free_terms_after t1 (dom psa) ->
    latest_term_before t2 psa = t1.
  Proof.
    intros Hlt Hsome Hfree.
    induction t2 as [| t IH]; first lia.
    rewrite /latest_term_before /=.
    destruct (decide (t = t1)) as [-> | Hne].
    { destruct Hsome as [v Hv]. by rewrite Hv. }
    assert (Ht1 : (t1 < t)%nat) by lia.
    rewrite /latest_term_before in IH.
    specialize (Hfree _ Ht1).
    rewrite not_elem_of_dom in Hfree.
    by rewrite Hfree (IH Ht1).
  Qed.

End lemma.

Section alloc.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Lemma paxos_inv_alloc addrm (fnames : gmap u64 byte_string) :
    let nids := dom addrm in
    (1 < size addrm)%nat ->
    dom fnames = dom addrm ->
    ([∗ map] fname ∈ fnames, fname f↦ []) -∗
    ([∗ set] addr ∈ map_img addrm, addr c↦ ∅) ==∗
    ∃ γ,
      (* give to client *)
      own_log_half γ [] ∗ own_cpool_half γ ∅ ∗
      (* give to paxos lock invariant *)
      ([∗ set] nid ∈ nids, own_current_term_half γ nid O) ∗
      ([∗ set] nid ∈ nids, own_ledger_term_half γ nid O) ∗
      ([∗ set] nid ∈ nids, own_committed_lsn_half γ nid O) ∗
      ([∗ set] nid ∈ nids, own_node_ledger_half γ nid []) ∗
      (* paxos atomic invariant *)
      (* TODO: also give [is_node_wal_fname] *)
      paxos_inv γ nids ∗ paxos_file_inv γ nids ∗ paxos_network_inv γ addrm.
  Proof.
    iIntros (nids Hmulti Hdomfnames) "Hfiles Hchans".
    iMod (paxos_res_alloc (dom addrm) fnames) as (γ) "(Hcs & Hps & Hpsb & Hnodesfn)".
    iDestruct "Hcs" as "(Hlog & Hlogcli & Hcpool & Hcpoolcli)".
    iDestruct "Hnodesfn" as "(Hlsnps & Hdss & Hpsas & Hpas & Hnodesfn)".
    iDestruct "Hnodesfn" as "(Htermcs & Htermcslk & Htermls & Htermlslk & Hnodesfn)".
    iDestruct "Hnodesfn" as "(Hlsncs & Hlsncslk & Hlogns & Hlognslk & Hfilenet)".
    iDestruct "Hfilenet" as "(Hwalfiles & Hwalnodes & #Hwalnames & Htrmls)".
    iFrame "Htermcslk Htermlslk Hlsncslk Hlognslk".
    iMod (proposal_insert O [] with "Hps") as "[Hps Hp]"; first done.
    iDestruct (proposal_witness with "Hp") as "#Hplb".
    iMod (base_proposal_insert O [] with "Hpsb") as "[Hpsb #Hpbrc]"; first done.
    (* Establish [safe_ledger_in γ nids O []] for use in global and node-local invariants.  *)
    iAssert (safe_ledger_in γ nids O [])%I as "#Hsafel".
    { unshelve epose proof (set_choose_L nids _) as [nid Hnid].
      { rewrite -fin_sets.size_non_empty_iff_L size_dom. lia. }
      iExists nid, nids.
      iSplit.
      { iDestruct (big_sepS_elem_of with "Hpas") as "Hpa"; first apply Hnid.
        iApply (accepted_proposal_witness with "Hpa").
      }
      iSplit.
      { iApply (big_sepS_mono with "Hpas").
        iIntros (nidx Hnidx) "Hpa".
        iDestruct (accepted_proposal_witness with "Hpa") as "#Hpalb".
        by iFrame "Hpalb".
      }
      iPureIntro.
      split; last apply Hnid.
      apply cquorum_refl.
      rewrite size_dom.
      lia.
    }
    iFrame "Hlog Hlogcli Hcpool Hcpoolcli Hps Hpsb".
    iAssert (paxos_file_inv γ (dom addrm))%I with "[Hfiles Hwalfiles]" as "Hpaxosfile".
    { rewrite /paxos_file_inv 2!big_sepS_big_sepM.
      rewrite (big_sepM_big_sepM2 _ addrm fnames); last done.
      do 2 (rewrite (big_sepM_big_sepM2 _ fnames addrm); last done).
      rewrite (big_sepM2_flip _ fnames).
      iCombine "Hfiles Hwalfiles" as "Hwalfiles".
      rewrite -big_sepM2_sep.
      iApply (big_sepM2_sepM_impl with "Hwalfiles"); first done.
      iIntros (nid fname c1 c2 Hfname Hc1 Hc2) "!> [Hfile Hwalflie]".
      iDestruct (big_sepM2_lookup with "Hwalnames") as "Hwalname".
      { apply Hfname. }
      { apply Hc1. }
      by iFrame "∗ #".
    }
    iAssert (paxos_network_inv γ addrm)%I with "[Htrmls Hchans]" as "Hpaxosnet".
    { (* Establish network invariant. *)
      iExists (gset_to_gmap ∅ (map_img addrm)), ∅.
      rewrite dom_empty_L.
      iFrame "Htrmls".
      iSplitL "Hchans".
      { iApply (big_sepS_sepM_impl with "Hchans"); first by rewrite dom_gset_to_gmap.
        iIntros (addr ms Hms) "!> Hchan".
        apply lookup_gset_to_gmap_Some in Hms as [_ <-].
        iExists ∅.
        iFrame "Hchan".
        by rewrite 3!set_map_empty 2!big_sepS_empty.
      }
      by rewrite big_sepM_empty dom_gset_to_gmap.
    }
    iFrame "Hpaxosfile Hpaxosnet".
    iModIntro.
    iExists (gset_to_gmap O nids).
    iSplit.
    { (* Partition the prepare LSNs. *)
      iAssert ([∗ set] nid ∈ nids, ([∗ set] t ∈ free_termps nid O, own_free_prepare_lsn γ t))%I
        with "[Hlsnps]" as "Hlsnps".
      { iDestruct (big_sepS_partition_1 _ _ nids (λ t nid, is_term_of_node nid t) with "Hlsnps")
          as "Hlsnps".
        { intros t nid1 nid2 Hne. by apply is_term_of_node_partitioned. }
        iApply (big_sepS_mono with "Hlsnps").
        iIntros (nid Hnid) "Hlsnps".
        iApply (big_sepS_subseteq with "Hlsnps").
        rewrite /free_termps.
        apply fin_sets.filter_subseteq_impl.
        by intros ? [_ ?].
      }
      iCombine "Hdss Hpsas Hpas Htermcs Htermls Hlsncs Hlogns Hlsnps Hwalnodes" as "Hnodes".
      rewrite -!big_sepS_sep.
      (* rewrite -{2}(dom_gset_to_gmap nids ([] : list nodedec)). *)
      rewrite big_sepS_big_sepM.
      iApply (big_sepM_impl_dom_eq with "Hnodes").
      { by rewrite !dom_gset_to_gmap. }
      iIntros (nid ds terml Hds Hterml).
      iIntros "!> (Hds & Hpsa & Hpa & Htermc & Hterml & Hlsnc & Hlogn & Hlsnp & Hwalnode)".
      apply lookup_gset_to_gmap_Some in Hterml as [_ <-].
      iFrame.
      iSplit.
      { rewrite big_sepM_singleton. by iFrame "Hpbrc". }
      iSplit.
      { rewrite big_sepM_singleton. by iFrame "Hplb". }
      iSplit.
      { rewrite take_0. by iFrame "Hsafel". }
      iPureIntro.
      split; first done.
      split; last done.
      { intros t Ht.
        rewrite dom_singleton_L not_elem_of_singleton.
        lia.
      }
    }
    iSplit.
    { iFrame "Hsafel". }
    iSplit.
    { by rewrite big_sepM_singleton /proposed_cmds big_sepL_nil. }
    iSplit.
    { rewrite big_sepM_singleton /safe_base_proposal.
      iExists (gset_to_gmap [] nids).
      iSplit.
      { set m := gset_to_gmap _ _.
        rewrite -{1}(dom_gset_to_gmap (dom addrm) ([] : list nodedec)).
        iDestruct (big_sepS_big_sepM _ m with "Hdss") as "Hdss".
        iApply (big_sepM_mono with "Hdss").
        iIntros (nid ds Hds) "Hds".
        apply lookup_gset_to_gmap_Some in Hds as [_ <-].
        by iApply (past_nodedecs_witness).
      }
      iPureIntro.
      split.
      { intros nid ds Hds.
        by apply lookup_gset_to_gmap_Some in Hds as [_ <-].
      }
      split.
      { rewrite /equal_latest_longest_proposal_nodedec /equal_latest_longest_proposal_with.
        by case_decide.
      }
      { rewrite dom_gset_to_gmap.
        apply cquorum_refl.
        rewrite size_dom.
        lia.
      }
    }
    iPureIntro.
    split.
    { by rewrite insert_empty /valid_proposals map_Forall2_singleton. }
    split.
    { by rewrite dom_gset_to_gmap. }
    split.
    { rewrite insert_empty dom_singleton_L.
      split; first apply is_term_of_node_partitioned.
      intros nid terml Hterml t Hton Hlt.
      rewrite not_elem_of_singleton.
      lia.
    }
    { by rewrite /cpool_subsume_log Forall_nil. }
  Qed.

End alloc.
