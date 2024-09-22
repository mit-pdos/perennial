From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import quorum list extend.
From Perennial.program_proof.tulip.paxos Require Import base res.

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

  Definition node_inv γ nid terml : iProp Σ :=
    ∃ ds psa termc logn,
      "Hds" ∷ own_past_nodedecs γ nid ds ∗
      "Hpsa"   ∷ own_accepted_proposals γ nid psa ∗
      "Htermc" ∷ own_current_term_half γ nid termc ∗
      "Hterml" ∷ own_ledger_term_half γ nid terml ∗
      "Hlogn"  ∷ own_node_ledger_half γ nid logn ∗
      "Hacpt"  ∷ own_accepted_proposal γ nid terml logn ∗
      "#Hpsalbs" ∷ ([∗ map] t ↦ v ∈ psa, prefix_base_ledger γ t v) ∗
      "#Hpsaubs" ∷ ([∗ map] t ↦ v ∈ psa, prefix_growing_ledger γ t v) ∗
      "%Hfixed"  ∷ ⌜fixed_proposals ds psa⌝ ∗
      "%Hdompsa" ∷ ⌜free_terms_after terml (dom psa)⌝ ∗
      "%Hlends"  ∷ ⌜length ds = termc⌝ ∗
      "%Htermlc" ∷ ⌜(terml ≤ termc)%nat⌝.

  Definition node_inv_without_ds_psa
    γ nid terml (ds : list nodedec) (psa : proposals) : iProp Σ :=
    ∃ termc logn,
      "Htermc" ∷ own_current_term_half γ nid termc ∗
      "Hterml" ∷ own_ledger_term_half γ nid terml ∗
      "Hlogn"  ∷ own_node_ledger_half γ nid logn ∗
      "Hacpt"  ∷ own_accepted_proposal γ nid terml logn ∗
      "%Hdompsa" ∷ ⌜free_terms_after terml (dom psa)⌝ ∗
      "%Hlends"  ∷ ⌜length ds = termc⌝ ∗
      "%Htermlc" ∷ ⌜(terml ≤ termc)%nat⌝.

  Definition node_inv_psa γ nid psa : iProp Σ :=
    "Hpsa"     ∷ own_accepted_proposals γ nid psa ∗
    "#Hpsalbs" ∷ ([∗ map] t ↦ v ∈ psa, prefix_base_ledger γ t v) ∗
    "#Hpsaubs" ∷ ([∗ map] t ↦ v ∈ psa, prefix_growing_ledger γ t v).

  Definition node_inv_ds_psa γ nid ds psa : iProp Σ :=
    "Hpsa"    ∷ node_inv_psa γ nid psa ∗
    "Hpastd"  ∷ own_past_nodedecs γ nid ds ∗
    "%Hfixed" ∷ ⌜fixed_proposals ds psa⌝.

  Lemma own_ledger_term_node_inv_terml_eq γ nid terml terml' :
    own_ledger_term_half γ nid terml -∗
    node_inv γ nid terml' -∗
    ⌜terml' = terml⌝.
  Proof.
    iIntros "HtermlX Hnode".
    iNamed "Hnode".
    by iDestruct (ledger_term_agree with "HtermlX Hterml") as %->.
  Qed.

  Definition prefix_of_accepted_proposal γ nid t logi: iProp Σ :=
    ∃ loga,
      "#Hloga"   ∷ is_accepted_proposal_lb γ nid t loga ∗
      "%Hprefix" ∷ ⌜prefix logi loga⌝.

  Definition safe_ledger γ nids logi : iProp Σ :=
    ∃ nidsq t,
      "#Hacpt"   ∷ ([∗ set] nid ∈ nidsq, prefix_of_accepted_proposal γ nid t logi) ∗
      "%Hquorum" ∷ ⌜cquorum nids nidsq⌝.

  Definition equal_latest_longest_proposal_nodedec (dssq : gmap u64 (list nodedec)) t v :=
    equal_latest_longest_proposal_with (mbind nodedec_to_ledger) dssq t v.

  Definition safe_base_proposal γ nids t v : iProp Σ :=
    ∃ dssqlb,
      "#Hdsq"    ∷ ([∗ map] nid ↦ ds ∈ dssqlb, is_past_nodedecs_lb γ nid ds) ∗
      "%Hlen"    ∷ ⌜map_Forall (λ _ ds, (t ≤ length ds)%nat) dssqlb⌝ ∗
      "%Hquorum" ∷ ⌜cquorum nids (dom dssqlb)⌝ ∗
      "%Heq"     ∷ ⌜equal_latest_longest_proposal_nodedec dssqlb t v⌝.

  Definition latest_term_before_nodedec t (ds : list nodedec) :=
    latest_term_before_with (mbind nodedec_to_ledger) t ds.

  Lemma latest_term_before_nodedec_unfold t ds :
    latest_term_before_nodedec t ds = latest_term_before_with (mbind nodedec_to_ledger) t ds.
  Proof. done. Qed.

  Definition latest_term_nodedec ds :=
    latest_term_before_nodedec (length ds) ds.

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
    destruct (dsslb !! nid) as [dslb |], (dss !! nid) as [ds |]; [| done | done | done].
    simpl. simpl in Hprefixes.
    f_equal.
    destruct Hprefixes as [[dsapp ->] Hlen].
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
    destruct (dss !! x) as [ds |], (bs !! x) as [ps |]; [| done | done | done].
    simpl.
    f_equal.
    destruct Hfixed as [Hfixed Hlen].
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
    destruct (dsslb !! nid) as [dslb |], (dss !! nid) as [ds |]; [| done | done | done].
    simpl. simpl in Hprefixes.
    f_equal.
    destruct Hprefixes as [Hprefix Hlen].
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
    destruct (dss !! x) as [ds |], (bs !! x) as [ps |]; [| done | done | done].
    simpl.
    f_equal.
    destruct Hfixed as [Hfixed Hlen].
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
      destruct (dss !! nid) as [ds |], (bs !! nid) as [ps |]; [| done | done | done].
      simpl. simpl in Hfixed.
      destruct Hfixed as [Hfixed Hlen].
      split; first done.
      subst t'.
      eapply Nat.lt_le_trans; last apply Hlen.
      by apply latest_term_before_quorum_with_lt.
    }
    done.
  Qed.

  Definition past_nodedecs_latest_before γ nid ds termc terml v : iProp Σ :=
    "#Hpastd"  ∷ is_past_nodedecs_lb γ nid ds ∗
    "%Hlends"  ∷ ⌜(termc ≤ length ds)%nat⌝ ∗
    "%Hlatest" ∷ ⌜latest_term_nodedec ds = terml⌝ ∗
    "%Hacpt"   ∷ ⌜ds !! terml = Some (Accept v)⌝.

  Definition paxos_inv γ nids : iProp Σ :=
    ∃ log cpool logi ps psb termlm,
      (* external states *)
      "Hlog"   ∷ own_log_half γ log ∗
      "Hcpool" ∷ own_cpool_half γ cpool ∗
      (* internal states *)
      "Hlogi" ∷ own_internal_log γ logi ∗
      "Hps"   ∷ own_proposals γ ps ∗
      "Hpsb"  ∷ own_base_proposals γ psb ∗
      (* node states *)
      "Hnodes" ∷ ([∗ map] nid ↦ terml ∈ termlm, node_inv γ nid terml) ∗
      (* TODO: constraints between internal and external states *)
      (* constraints on internal states *)
      "#Hsafelogi"  ∷ safe_ledger γ nids logi ∗
      "#Hsafepsb"   ∷ ([∗ map] t ↦ v ∈ psb, safe_base_proposal γ nids t v) ∗
      "%Hvp"        ∷ ⌜valid_proposals ps psb⌝ ∗
      "%Hdomtermlm" ∷ ⌜dom termlm = nids⌝ ∗
      "%Hdompsb"    ∷ ⌜free_terms (dom psb) termlm⌝.

  #[global]
  Instance paxos_inv_timeless γ nids :
    Timeless (paxos_inv γ nids).
  Admitted.

  Definition know_paxos_inv γ nids : iProp Σ :=
    inv paxosNS (paxos_inv γ nids).

End inv.
