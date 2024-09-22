From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm Require Import big_sep.
From Perennial.program_proof.rsm.pure Require Import quorum extend list.
From Perennial.program_proof.tulip.paxos Require Import base consistency.

Section res.
  Context `{!paxos_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : paxos_names).

  Section consensus.

    (** Elements. *)

    Definition own_log_half γ (l : ledger) : iProp Σ.
    Admitted.

    Definition is_log_lb γ (l : ledger) : iProp Σ.
    Admitted.

    Definition own_cpool_half γ (vs : gset string) : iProp Σ.
    Admitted.

    (** Type class instances. *)

    #[global]
    Instance is_log_lb_persistent γ l :
      Persistent (is_log_lb γ l).
    Admitted.

    (** Rules. *)

    Lemma log_update {γ} l1 l2 vs :
      Forall (λ v, v ∈ vs) l2 ->
      prefix l1 l2 ->
      own_log_half γ l1 -∗
      own_log_half γ l1 -∗
      own_cpool_half γ vs ==∗
      own_log_half γ l2 ∗ own_log_half γ l2 ∗ own_cpool_half γ vs.
    Admitted.

    Lemma log_witness {γ l} :
      own_log_half γ l -∗
      is_log_lb γ l.
    Admitted.

    Lemma log_prefix {γ l lb} :
      own_log_half γ l -∗
      is_log_lb γ lb -∗
      ⌜prefix lb l⌝.
    Admitted.

    Lemma log_lb_prefix {γ lb1 lb2} :
      is_log_lb γ lb1 -∗
      is_log_lb γ lb2 -∗
      ⌜prefix lb1 lb2 ∨ prefix lb2 lb1⌝.
    Admitted.

    Lemma cpool_update {γ vs1} vs2 :
      vs1 ⊆ vs2 ->
      own_cpool_half γ vs1 -∗
      own_cpool_half γ vs1 ==∗
      own_cpool_half γ vs2 ∗ own_cpool_half γ vs2.
    Admitted.

    Definition cpool_subsume_log (l : ledger) (vs : gset string) :=
      Forall (λ v, v ∈ vs) l.

    Lemma consensus_incl {γ l vs} :
      own_log_half γ l -∗
      own_cpool_half γ vs -∗
      ⌜cpool_subsume_log l vs⌝.
    Admitted.

  End consensus.

  Section internal_log.

    (** Elements. *)

    Definition own_internal_log γ (l : ledger) : iProp Σ.
    Admitted.

    Definition is_internal_log_lb γ (l : ledger) : iProp Σ.
    Admitted.

    (** Type class instances. *)

    #[global]
    Instance is_internal_log_lb_persistent γ l :
      Persistent (is_internal_log_lb γ l).
    Admitted.

    (** Rules. *)

    Lemma internal_log_update {γ l1} l2 :
      prefix l1 l2 ->
      own_internal_log γ l1 ==∗
      own_internal_log γ l2.
    Admitted.

    Lemma internal_log_witness {γ l} lb :
      prefix lb l ->
      own_internal_log γ l -∗
      is_internal_log_lb γ lb.
    Admitted.

    Lemma internal_log_prefix {γ l lb} :
      own_internal_log γ l -∗
      is_internal_log_lb γ lb -∗
      ⌜prefix lb l⌝.
    Admitted.

  End internal_log.

  Section proposal.

    (** Elements. *)

    Definition own_proposals γ (ps : proposals) : iProp Σ.
    Admitted.

    Definition own_proposal γ (t : nat) (v : ledger) : iProp Σ.
    Admitted.

    Definition is_proposal_lb γ (t : nat) (v : ledger) : iProp Σ.
    Admitted.

    (** Type class instances. *)

    #[global]
    Instance is_proposal_lb_persistent γ t v :
      Persistent (is_proposal_lb γ t v).
    Admitted.

    (** Rules. *)

    Lemma proposal_insert {γ ps} t v :
      ps !! t = None ->
      own_proposals γ ps ==∗
      own_proposals γ (<[t := v]> ps) ∗ own_proposal γ t v.
    Admitted.

    Lemma proposal_lookup {γ ps t v} :
      own_proposal γ t v -∗
      own_proposals γ ps -∗
      ⌜ps !! t = Some v⌝.
    Admitted.

    Lemma proposal_update {γ ps t v1} v2 :
      prefix v1 v2 ->
      own_proposal γ t v1 -∗
      own_proposals γ ps ==∗
      own_proposal γ t v2 ∗ own_proposals γ (<[t := v2]> ps).
    Admitted.

    Lemma proposal_witness {γ t v} :
      own_proposal γ t v -∗
      is_proposal_lb γ t v.
    Admitted.

    Lemma proposal_prefix {γ ps t vlb} :
      is_proposal_lb γ t vlb -∗
      own_proposals γ ps -∗
      ∃ v, ⌜ps !! t = Some v ∧ prefix vlb v⌝.
    Admitted.

  End proposal.

  Section base_proposal.

    (** Elements. *)

    Definition own_base_proposals γ (ps : proposals) : iProp Σ.
    Admitted.

    Definition is_base_proposal_receipt γ (t : nat) (v : ledger) : iProp Σ.
    Admitted.

    (** Type class instances. *)

    #[global]
    Instance is_base_proposal_receipt_persistent γ t v :
      Persistent (is_base_proposal_receipt γ t v).
    Admitted.

    (** Rules. *)

    Lemma base_proposal_insert {γ ps} t v :
      ps !! t = None ->
      own_base_proposals γ ps ==∗
      own_base_proposals γ (<[t := v]> ps) ∗ is_base_proposal_receipt γ t v.
    Admitted.

    Lemma base_proposal_lookup {γ ps t v} :
      is_base_proposal_receipt γ t v -∗
      own_base_proposals γ ps -∗
      ⌜ps !! t = Some v⌝.
    Admitted.

  End base_proposal.

  Section past_nodedecs.

    (** Elements. *)

    Definition own_past_nodedecs γ (nid : u64) (d : list nodedec) : iProp Σ.
    Admitted.

    Definition is_past_nodedecs_lb γ (nid : u64) (d : list nodedec) : iProp Σ.
    Admitted.

    (** Type class instances. *)

    #[global]
    Instance is_past_nodedecs_lb_persistent γ nid d :
      Persistent (is_past_nodedecs_lb γ nid d).
    Admitted.

    (** Rules. *)

    Lemma past_nodedecs_update {γ nid d1} d2 :
      prefix d1 d2 ->
      own_past_nodedecs γ nid d1 ==∗
      own_past_nodedecs γ nid d2.
    Admitted.

    Lemma past_nodedecs_witness γ nid d :
      own_past_nodedecs γ nid d -∗
      is_past_nodedecs_lb γ nid d.
    Admitted.

    Lemma past_nodedecs_prefix γ nid dlb d :
      is_past_nodedecs_lb γ nid dlb -∗
      own_past_nodedecs γ nid d -∗
      ⌜prefix dlb d⌝.
    Admitted.

  End past_nodedecs.

  Section accepted_proposal.

    (** Elements. *)

    Definition own_accepted_proposals γ (nid : u64) (ps : proposals) : iProp Σ.
    Admitted.

    Definition own_accepted_proposal γ (nid : u64) (t : nat) (v : ledger) : iProp Σ.
    Admitted.

    Definition is_accepted_proposal_lb γ (nid : u64) (t : nat) (v : ledger) : iProp Σ.
    Admitted.

    (** Type class instances. *)

    #[global]
    Instance is_accepted_proposal_lb_persistent γ nid t v :
      Persistent (is_accepted_proposal_lb γ nid t v).
    Admitted.

    (** Rules. *)

    Lemma accepted_proposal_insert {γ nid ps} t v :
      ps !! t = None ->
      own_accepted_proposals γ nid ps ==∗
      own_accepted_proposals γ nid (<[t := v]> ps) ∗ own_accepted_proposal γ nid t v.
    Admitted.

    Lemma accepted_proposal_update {γ nid ps t v1} v2 :
      prefix v1 v2 ->
      own_accepted_proposal γ nid t v1 -∗
      own_accepted_proposals γ nid ps ==∗
      own_accepted_proposal γ nid t v2 ∗ own_accepted_proposals γ nid (<[t := v2]> ps).
    Admitted.

    Lemma accepted_proposal_lookup {γ nid ps t v} :
      own_accepted_proposal γ nid t v -∗
      own_accepted_proposals γ nid ps -∗
      ⌜ps !! t = Some v⌝.
    Admitted.

    Lemma accepted_proposal_witness {γ nid t v} :
      own_accepted_proposal γ nid t v -∗
      is_accepted_proposal_lb γ nid t v.
    Admitted.

    Lemma accepted_proposal_prefix {γ nid ps t vlb} :
      is_accepted_proposal_lb γ nid t vlb -∗
      own_accepted_proposals γ nid ps -∗
      ∃ v, ⌜ps !! t = Some v ∧ prefix vlb v⌝.
    Admitted.

  End accepted_proposal.

  Section current_term.

    (** Elements. *)

    Definition own_current_term_half γ (nid : u64) (t : nat) : iProp Σ.
    Admitted.

    (** Type class instances. *)

    (** Rules. *)

    Lemma current_term_update {γ nid t1} t2 :
      own_current_term_half γ nid t1 -∗
      own_current_term_half γ nid t1 ==∗
      own_current_term_half γ nid t2 ∗ own_current_term_half γ nid t2.
    Admitted.

    Lemma current_term_agree {γ nid t1 t2} :
      own_current_term_half γ nid t1 -∗
      own_current_term_half γ nid t2 -∗
      ⌜t2 = t1⌝.
    Admitted.

  End current_term.

  Section ledger_term.

    (** Elements. *)

    Definition own_ledger_term_half γ (nid : u64) (t : nat) : iProp Σ.
    Admitted.

    (** Type class instances. *)

    (** Rules. *)

    Lemma ledger_term_update {γ nid t1} t2 :
      own_ledger_term_half γ nid t1 -∗
      own_ledger_term_half γ nid t1 ==∗
      own_ledger_term_half γ nid t2 ∗ own_ledger_term_half γ nid t2.
    Admitted.

    Lemma ledger_term_agree {γ nid t1 t2} :
      own_ledger_term_half γ nid t1 -∗
      own_ledger_term_half γ nid t2 -∗
      ⌜t2 = t1⌝.
    Admitted.

  End ledger_term.

  Section node_ledger.

    (** Elements. *)

    Definition own_node_ledger_half γ (nid : u64) (v : ledger) : iProp Σ.
    Admitted.

    (** Type class instances. *)

    (** Rules. *)

    Lemma node_ledger_update {γ nid v1} v2 :
      own_node_ledger_half γ nid v1 -∗
      own_node_ledger_half γ nid v1 ==∗
      own_node_ledger_half γ nid v2 ∗ own_node_ledger_half γ nid v2.
    Admitted.

    Lemma node_ledger_agree {γ nid v1 v2} :
      own_node_ledger_half γ nid v1 -∗
      own_node_ledger_half γ nid v2 -∗
      ⌜v2 = v1⌝.
    Admitted.

  End node_ledger.

End res.

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

Section prepare.
  Context `{!paxos_ghostG Σ}.

  Lemma fixed_proposals_inv_prepare_term_lt psa termc' terml ds :
    let ds' := extend termc' Reject ds in
    (terml < length ds < termc')%nat ->
    free_terms_after terml (dom psa) ->
    fixed_proposals ds psa ->
    fixed_proposals ds' psa.
  Proof.
    intros ds' Horder Hfree Hfp t d Hd.
    destruct (decide (t < length ds)%nat) as [Hlt | Hge].
    { rewrite lookup_extend_l in Hd; last apply Hlt.
      by specialize (Hfp _ _ Hd).
    }
    rewrite Nat.nlt_ge in Hge.
    assert (Htlt : (t < termc')%nat).
    { apply lookup_lt_Some in Hd. rewrite extend_length in Hd. lia. }
    rewrite lookup_extend_r in Hd; last lia.
    inv Hd.
    assert (Htgt : (terml < t)%nat) by lia.
    specialize (Hfree _ Htgt).
    rewrite not_elem_of_dom in Hfree.
    by rewrite Hfree.
  Qed.

  Lemma fixed_proposals_inv_prepare_term_eq psa termc termc' ds v :
    let ds' := extend termc' Reject (ds ++ [Accept v]) in
    length ds = termc ->
    (termc < termc')%nat ->
    psa !! termc = Some v ->
    free_terms_after termc (dom psa) ->
    fixed_proposals ds psa ->
    fixed_proposals ds' psa.
  Proof.
    intros ds' Hlends Horder Hv Hfree Hfp t d Hd.
    destruct (decide (t < length ds)%nat) as [Hlt | Hge].
    { rewrite lookup_extend_l in Hd; last first.
      { rewrite last_length. lia. }
      rewrite lookup_app_l in Hd; last apply Hlt.
      by specialize (Hfp _ _ Hd).
    }
    rewrite Nat.nlt_ge in Hge.
    destruct (decide (t = length ds)) as [Heq | Hne].
    { subst t.
      rewrite Hlends Hv.
      rewrite lookup_extend_l in Hd; last first.
      { rewrite last_length. lia. }
      rewrite lookup_snoc_length in Hd.
      by inv Hd.
    }
    assert (Htgt : (length ds < t)%nat) by lia.
    assert (Htlt : (t < termc')%nat).
    { apply lookup_lt_Some in Hd. rewrite extend_length last_length in Hd. lia. }
    rewrite lookup_extend_r in Hd; last first.
    { rewrite last_length. lia. }
    inv Hd.
    specialize (Hfree _ Htgt).
    rewrite not_elem_of_dom in Hfree.
    by rewrite Hfree.
  Qed.

  Lemma latest_term_nodedec_snoc_Accept ds v :
    latest_term_nodedec (ds ++ [Accept v]) = length ds.
    rewrite /latest_term_nodedec /latest_term_before_nodedec last_length /= lookup_app_r; last done.
    by replace (_ - _)%nat with O by lia.
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

  Lemma node_inv_prepare γ nid termc termc' terml v :
    (termc < termc')%nat ->
    own_current_term_half γ nid termc -∗
    own_node_ledger_half γ nid v -∗
    node_inv γ nid terml ==∗
    own_current_term_half γ nid termc' ∗
    own_node_ledger_half γ nid v ∗
    node_inv γ nid terml ∗
    ∃ d, past_nodedecs_latest_before γ nid d termc' terml v.
  Proof.
    iIntros (Hlt) "HtermcX Hv Hinv".
    iNamed "Hinv".
    iDestruct (current_term_agree with "HtermcX Htermc") as %->.
    iDestruct (node_ledger_agree with "Hv Hlogn") as %->.
    iDestruct (accepted_proposal_lookup with "Hacpt Hpsa") as %Hv.
    destruct (decide (terml = termc)) as [-> | Hne]; last first.
    { (* Case: [terml < termc] iff no ledger accepted at [termc] yet. *)
      (* Update the current term [termc] to [termc']. *)
      iMod (current_term_update termc' with "HtermcX Htermc") as "[HtermcX Htermc]".
      (* Extend the node decisions [d] with [Reject]. *)
      set ds' := extend termc' Reject ds.
      iMod (past_nodedecs_update ds' with "Hds") as "Hds".
      { apply extend_prefix. }
      (* Extract a witness of the extended past decision. *)
      iDestruct (past_nodedecs_witness with "Hds") as "#Hdlb".
      (* Re-establish [fixed_proposals d' psa]. *)
      unshelve epose proof
        (fixed_proposals_inv_prepare_term_lt _ termc' _ ds _ Hdompsa Hfixed) as Hfixed'.
      { clear -Hlt Htermlc Hlends Hne. lia. }
      iFrame "∗ # %".
      iPureIntro.
      split.
      { rewrite extend_length. lia. }
      split.
      { rewrite extend_length. lia. }
      split; last first.
      { rewrite lookup_extend_l; last lia.
        unshelve epose proof (list_lookup_lt ds terml _) as [d Hd]; first lia.
        specialize (Hfixed _ _ Hd).
        rewrite Hd.
        rewrite Hfixed in Hv.
        apply nodedec_to_ledger_Some_inv in Hv.
        by rewrite Hv.
      }
      rewrite latest_term_nodedec_extend_Reject.
      unshelve epose proof (free_terms_after_latest_term_before _ _ termc _ _ Hdompsa) as Hlatest.
      { lia. }
      { done. }
      rewrite /latest_term_nodedec Hlends.
      unshelve erewrite (fixed_proposals_latest_term_before_nodedec _ _ _ _ Hfixed); [lia | done].
    }
    (* Case: [terml = termc] iff ledger [v] accepted at [termc]. *)
    (* Update the current term [termc] to [termc']. *)
    iMod (current_term_update termc' with "HtermcX Htermc") as "[HtermcX Htermc]".
    (* Snoc [Accept v] and extend the node decisions [d] with [Reject]. *)
    set ds' := extend termc' Reject (ds ++ [Accept v]).
    iMod (past_nodedecs_update ds' with "Hds") as "Hds".
    { etrans; last apply extend_prefix.
      by apply prefix_app_r.
    }
    (* Extract a witness of the extended past decision. *)
    iDestruct (past_nodedecs_witness with "Hds") as "#Hdlb".
    unshelve epose proof
      (fixed_proposals_inv_prepare_term_eq _ _ _ _ _ Hlends Hlt Hv Hdompsa Hfixed) as Hfixed'.
    iFrame "∗ # %".
    iPureIntro.
    split.
    { rewrite extend_length last_length. lia. }
    split.
    { rewrite extend_length. lia. }
    split; last first.
    { rewrite lookup_extend_l; last first.
      { rewrite last_length. lia. }
      by rewrite -Hlends lookup_snoc_length.
    }
    by rewrite latest_term_nodedec_extend_Reject latest_term_nodedec_snoc_Accept.
  Qed.

  Lemma paxos_inv_prepare γ nids nid termc termc' terml v :
    nid ∈ nids ->
    (termc < termc')%nat ->
    own_current_term_half γ nid termc -∗
    own_ledger_term_half γ nid terml -∗
    own_node_ledger_half γ nid v -∗
    paxos_inv γ nids ==∗
    own_current_term_half γ nid termc' ∗
    own_ledger_term_half γ nid terml ∗
    own_node_ledger_half γ nid v ∗
    paxos_inv γ nids ∗
    ∃ d, past_nodedecs_latest_before γ nid d termc' terml v.
  Proof.
    iIntros (Hnid Hlt) "Htermc Hterml Hv Hinv".
    iNamed "Hinv".
    rewrite -Hdomtermlm elem_of_dom in Hnid.
    destruct Hnid as [terml' Hterml'].
    iDestruct (big_sepM_lookup_acc _ _ nid with "Hnodes") as "[Hnode HnodesC]".
    { apply Hterml'. }
    iDestruct (own_ledger_term_node_inv_terml_eq with "Hterml Hnode") as %->.
    iMod (node_inv_prepare _ _ _ _ _ _ Hlt with "Htermc Hv Hnode")
      as "(Htermc & Hv & Hnode & #Hpast)".
    iDestruct ("HnodesC" with "Hnode") as "Hnodes".
    by iFrame "∗ # %".
  Qed.

End prepare.

Section commit.
  Context `{!paxos_ghostG Σ}.

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
      { done. }
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
      by specialize (Hlen _ _ Hdslb).
    }
    pose proof (equal_latest_longest_proposal_nodedec_prefix _ _ _ _ Hprefix Heq) as Heq'.
    iAssert (⌜map_Forall2 (λ _ ds psa, fixed_proposals ds psa ∧ (t ≤ length ds)%nat) dssq bsq⌝)%I
      as %Hfixed.
    { iIntros (x).
      destruct (dssq !! x) as [ds |] eqn:Hds, (bsq !! x) as [psa |] eqn:Hpsa; last first.
      { done. }
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
      split; first apply Hfixed.
      destruct Hprefix as [Hprefix Hlelen].
      apply prefix_length in Hprefix.
      lia.
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
    iDestruct (proposal_prefix with "Hvub Hps") as %(vub & Hvub & Hprefixvlb).
    iPureIntro.
    exists vub.
    split; first apply Hvub.
    by trans vlb.
  Qed.

  Lemma node_inv_extract_ds_psa γ nid terml :
    node_inv γ nid terml -∗
    ∃ ds psa, node_inv_without_ds_psa γ nid terml ds psa ∗
              node_inv_ds_psa γ nid ds psa.
  Proof. iIntros "Hinv". iNamed "Hinv". iFrame "∗ # %". Qed.

  Lemma nodes_inv_extract_ds_psa γ termlm :
    ([∗ map] nid ↦ terml ∈ termlm, node_inv γ nid terml) -∗
    ∃ dss bs, ([∗ map] nid ↦ terml; dp ∈ termlm; map_zip dss bs,
                 node_inv_without_ds_psa γ nid terml dp.1 dp.2) ∗
              ([∗ map] nid ↦ ds; psa ∈ dss; bs, node_inv_ds_psa γ nid ds psa).
  Proof.
    iIntros "Hinvs".
    set Φ := (λ nid terml dp,
                node_inv_without_ds_psa γ nid terml dp.1 dp.2 ∗
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

  Lemma nodes_inv_merge_ds_psa γ termlm dss bs :
    ([∗ map] nid ↦ terml; dp ∈ termlm; map_zip dss bs,
       node_inv_without_ds_psa γ nid terml dp.1 dp.2) -∗
    ([∗ map] nid ↦ ds; psa ∈ dss; bs, node_inv_ds_psa γ nid ds psa) -∗
    ([∗ map] nid ↦ terml ∈ termlm, node_inv γ nid terml).
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

  Lemma nodes_inv_safe_ledger_impl_chosen γ nids bs v :
    dom bs = nids ->
    ([∗ map] nid ↦ psa ∈ bs, node_inv_psa γ nid psa) -∗
    safe_ledger γ nids v -∗
    ⌜chosen bs v⌝.
  Proof.
    iIntros (Hdombs) "Hinv Hv".
    iNamed "Hv".
    set bsq := (filter (λ x, x.1 ∈ nidsq) bs).
    iExists t, bsq.
    rewrite base.and_assoc.
    iSplit.
    { iPureIntro.
      split; first apply map_filter_subseteq.
      rewrite Hdombs.
      subst bsq.
      destruct Hquorum as [Hincl Hquorum].
      rewrite (dom_filter_L _ _ nidsq); first apply Hquorum.
      intros nid.
      split; last by intros (ps & _ & Hin).
      intros Hin.
      assert (is_Some (bs !! nid)) as [ps Hps].
      { rewrite -elem_of_dom Hdombs. set_solver. }
      by exists ps.
    }
    iIntros (nid ps Hps).
    iDestruct (big_sepS_elem_of _ _ nid with "Hacpt") as "Hprefix".
    { by apply map_lookup_filter_Some_1_2 in Hps. }
    iNamed "Hprefix".
    iDestruct (big_sepM_lookup _ _ nid with "Hinv") as "Hnid".
    { eapply lookup_weaken; [apply Hps | apply map_filter_subseteq]. }
    iNamed "Hnid".
    iDestruct (accepted_proposal_prefix with "Hloga Hpsa") as %(va & Hva & Hprefixva).
    iPureIntro.
    exists va.
    split; first apply Hva.
    by trans loga.
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

  Lemma paxos_inv_commit γ nids logi' :
    safe_ledger γ nids logi' -∗
    paxos_inv γ nids ==∗
    paxos_inv γ nids ∗
    is_internal_log_lb γ logi'.
  Proof.
    iIntros "#Hsafe Hinv".
    iNamed "Hinv".
    (* Extract past decisions and accepted proposals from the node invariant. *)
    iDestruct (nodes_inv_extract_ds_psa with "Hnodes") as (dss bs) "[Hnodes Hpds]".
    iDestruct (big_sepM2_dom with "Hpds") as %Hdompds.
    iDestruct (big_sepM2_dom with "Hnodes") as %Hdombs.
    rewrite dom_map_zip_with_L Hdompds Hdomtermlm in Hdombs. symmetry in Hdombs.
    replace (_ ∩ _) with (dom bs) in Hdombs by set_solver.
    (* not sure why the following fails, so using replace above as a workaround *)
    (* rewrite intersection_idemp in Hdombs. *)
    (* Obtain [valid_base_proposals bs psb]. *)
    iDestruct (nodes_inv_impl_valid_base_proposals with "Hsafepsb Hpds") as %Hvbp.
    { apply Hdombs. }
    (* Obtain [nodes_inv_valid_lb_ballots bs psb]. *)
    iDestruct (nodes_inv_impl_valid_lb_ballots _ bs with "Hpsb [Hpds]") as %Hvlb.
    { by iApply nodes_inv_ds_psa_impl_nodes_inv_psa. }
    (* Obtain [nodes_inv_valid_ub_ballots bs ps]. *)
    iDestruct (nodes_inv_impl_valid_ub_ballots _ bs with "Hps [Hpds]") as %Hvub.
    { by iApply nodes_inv_ds_psa_impl_nodes_inv_psa. }
    (* Finally, derive [consistency bs]. *)
    pose proof (vlb_vub_vbp_vp_impl_consistency _ _ _ Hvlb Hvub Hvbp Hvp) as Hcst.
    (* Now, derive [chosen bs logi] and [chosen bs logi']. *)
    iDestruct (nodes_inv_safe_ledger_impl_chosen _ _ bs with "[Hpds] Hsafelogi") as %Hchosen.
    { apply Hdombs. }
    { by iApply nodes_inv_ds_psa_impl_nodes_inv_psa. }
    iDestruct (nodes_inv_safe_ledger_impl_chosen _ _ bs with "[Hpds] Hsafe") as %Hchosen'.
    { apply Hdombs. }
    { by iApply nodes_inv_ds_psa_impl_nodes_inv_psa. }
    (* Derive [prefix logi logi' ∨ prefix logi' logi]. *)
    specialize (Hcst _ _ Hchosen Hchosen').
    (* Merge [node_inv_ds_psa] back. *)
    iDestruct (nodes_inv_merge_ds_psa with "Hnodes Hpds") as "Hnodes".
    destruct Hcst as [Hge | Hle]; last first.
    { (* Case: The old log is at least as long as the new log. Simply extract a witness. *)
      iDestruct (internal_log_witness logi' with "Hlogi") as "#Hlb"; first apply Hle.
      by iFrame "∗ # %".
    }
    (* Case: The new log is at least as long as the old log. Update the log. *)
    iMod (internal_log_update with "Hlogi") as "Hlogi"; first apply Hge.
    iDestruct (internal_log_witness logi' with "Hlogi") as "#Hlb"; first done.
    by iFrame "∗ # %".
  Qed.

End commit.

Lemma free_terms_inv_ascend {nid ts tm} termc :
  gt_prev_term tm nid termc ->
  is_term_of_node nid termc ->
  free_terms ts tm ->
  free_terms ({[termc]} ∪ ts) (<[nid := termc]> tm).
Proof.
  intros Hprev Htermc [Hdisj Hfree].
  split; first done.
  intros nidx t Ht t' Ht' Hlt.
  destruct (decide (nidx = nid)) as [-> | Hne]; last first.
  { destruct (decide (t' = termc)) as [-> | Hne'].
    { by specialize (Hdisj _ _ _ Hne Ht'). }
    rewrite lookup_insert_ne in Ht; last done.
    specialize (Hfree _ _ Ht _ Ht' Hlt).
    set_solver.
  }
  rewrite lookup_insert in Ht.
  symmetry in Ht. inv Ht.
  destruct Hprev as (termp & Htermp & Htermpc).
  assert (Hlt' : (termp < t')%nat) by lia.
  specialize (Hfree _ _ Htermp _ Ht' Hlt').
  assert (Hne : t' ≠ termc) by lia.
  set_solver.
Qed.

Section ascend.
  Context `{!paxos_ghostG Σ}.

  Lemma node_inv_ascend {γ nid termc terml logn} logn' :
    (terml < termc)%nat ->
    prefix_base_ledger γ termc logn' -∗
    prefix_growing_ledger γ termc logn' -∗
    own_current_term_half γ nid termc -∗
    own_ledger_term_half γ nid terml -∗
    own_node_ledger_half γ nid logn -∗
    node_inv γ nid terml ==∗
    own_current_term_half γ nid termc ∗
    own_ledger_term_half γ nid termc ∗
    own_node_ledger_half γ nid logn' ∗
    node_inv γ nid termc ∗
    is_accepted_proposal_lb γ nid termc logn'.
  Proof.
    iIntros (Hlt) "#Hpfb #Hpfg HtermcX HtermlX HlognX Hinv".
    iNamed "Hinv".
    (* Agreements on the current term and the node ledger. *)
    iDestruct (current_term_agree with "HtermcX Htermc") as %->.
    iDestruct (node_ledger_agree with "HlognX Hlogn") as %->.
    (* Update the ledger term to [termc]. *)
    iMod (ledger_term_update termc with "HtermlX Hterml") as "[HtermlX Hterml]".
    (* Update the current ledger to [logn']. *)
    iMod (node_ledger_update logn' with "HlognX Hlogn") as "[HlognX Hlogn]".
    (* Insert [(termc, logn')] into the accepted proposals. *)
    iMod (accepted_proposal_insert termc logn' with "Hpsa") as "[Hpsa Hp]".
    { specialize (Hdompsa _ Hlt). by rewrite -not_elem_of_dom. }
    iDestruct (accepted_proposal_witness with "Hp") as "#Hplb".
    iClear "Hacpt".
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { by iApply big_sepM_insert_2. }
    iSplit.
    { by iApply big_sepM_insert_2. }
    iPureIntro.
    split.
    { (* Re-establish [fixed_proposals]. *)
      intros t d Hd.
      destruct (decide (t = termc)) as [-> | Hne]; last first.
      { rewrite lookup_insert_ne; last done.
        by specialize (Hfixed _ _ Hd).
      }
      rewrite lookup_insert.
      exfalso.
      (* Derive contradiction from [Hlends] and [Hd]. *)
      apply lookup_lt_Some in Hd.
      lia.
    }
    split.
    { (* Re-establish [free_terms_after]. *)
      rewrite dom_insert_L.
      intros t Hgttermc.
      assert (Hgtterml : (terml < t)%nat) by lia.
      specialize (Hdompsa _ Hgtterml).
      assert (Hne : t ≠ termc) by lia.
      set_solver.
    }
    done.
  Qed.

  Lemma paxos_inv_ascend γ nids nid termc terml logn logn' :
    nid ∈ nids ->
    is_term_of_node nid termc ->
    (terml < termc)%nat ->
    safe_base_proposal γ nids termc logn' -∗
    own_current_term_half γ nid termc -∗
    own_ledger_term_half γ nid terml -∗
    own_node_ledger_half γ nid logn -∗
    paxos_inv γ nids ==∗
    own_current_term_half γ nid termc ∗
    own_ledger_term_half γ nid termc ∗
    own_node_ledger_half γ nid logn' ∗
    paxos_inv γ nids ∗
    own_proposal γ termc logn' ∗
    is_base_proposal_receipt γ termc logn' ∗
    is_accepted_proposal_lb γ nid termc logn'.
  Proof.
    iIntros (Hnid Hton Hlt) "Hsafe Htermc Hterml Hlogn Hinv".
    iNamed "Hinv".
    pose proof Hnid as Hterml.
    rewrite -Hdomtermlm elem_of_dom in Hterml.
    destruct Hterml as [terml' Hterml].
    iDestruct (big_sepM_delete _ _ nid with "Hnodes") as "[Hnode Hnodes]".
    { apply Hterml. }
    iDestruct (own_ledger_term_node_inv_terml_eq with "Hterml Hnode") as %->.
    (* Obtain freshness of [termc] before insertion to growing / base proposals. *)
    assert (Hnotin : termc ∉ dom psb).
    { rewrite /free_terms /free_terms_with_partf in Hdompsb.
      destruct Hdompsb as [_ Hfree].
      by specialize (Hfree _ _ Hterml _ Hton Hlt).
    }
    (* Insert [(termc, logn')] into the growing proposals and the base proposals. *)
    iMod (proposal_insert termc logn' with "Hps") as "[Hps Hp]".
    { apply map_Forall2_dom_L in Hvp as Hdomps. by rewrite Hdomps not_elem_of_dom in Hnotin. }
    iMod (base_proposal_insert termc logn' with "Hpsb") as "[Hpsb #Hpsbrcp]".
    { by rewrite not_elem_of_dom in Hnotin. }
    (* Extract witness of the inserted proposal to re-establish the node invariant. *)
    iDestruct (proposal_witness with "Hp") as "#Hplb".
    (* Re-establish node invariant. *)
    iMod (node_inv_ascend logn' with "[] [] Htermc Hterml Hlogn Hnode")
      as "(Htermc & Hterml & Hlogn & Hnode & #Hacptlb)".
    { apply Hlt. }
    { by iFrame "Hpsbrcp". }
    { by iFrame "Hplb". }
    iDestruct (big_sepM_insert_2 with "Hnode Hnodes") as "Hnodes".
    rewrite insert_delete_insert.
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { (* Re-establish [safe_base_proposal]. *)
      iApply (big_sepM_insert_2 with "Hsafe Hsafepsb").
    }
    iPureIntro.
    split.
    { (* Re-establish [valid_proposals]. *)
      by apply map_Forall2_insert_2.
    }
    split.
    { (* Reestablish that domain of [termlm] equals to [nids]. *)
      rewrite dom_insert_L.
      set_solver.
    }
    { (* Re-establish [free_terms]. *)
      rewrite dom_insert_L.
      apply free_terms_inv_ascend; [| done | done].
      rewrite /gt_prev_term.
      by eauto.
    }
  Qed.

End ascend.

(**
 * Notes on state-machine actions of Paxos:
 * - ascend(t, v): insert [(t, v)] into [proposals] and [base_proposals].
 * - extend(t, v): update [proposals !! t] to [v]
 * - prepare(t): snoc [accepted_proposals !! (length ballot)] to [ballot] if it exists, and extend [ballot] with [Reject] up to [t].
 * - advance(t, v): insert [(t, v)] into [accepted_proposals].
 * - accept(t, v): update [accepted_proposals !! t] to [v].
 * - commit(v): update [internal_log] to [v].
 *)

Section extend.
  Context `{!paxos_ghostG Σ}.

  Lemma paxos_inv_extend γ nids term logn logn' :
    prefix logn logn' ->
    own_proposal γ term logn -∗
    paxos_inv γ nids ==∗
    own_proposal γ term logn' ∗
    paxos_inv γ nids ∗
    is_proposal_lb γ term logn'.
  Proof.
    iIntros (Hprefix) "Hp Hinv".
    iNamed "Hinv".
    iDestruct (proposal_lookup with "Hp Hps") as %Hlogn.
    (* Extend the growing proposal to [logn'] and extract a witness. *)
    iMod (proposal_update logn' with "Hp Hps") as "[Hp Hps]"; first apply Hprefix.
    iDestruct (proposal_witness with "Hp") as "#Hplb".
    iFrame "∗ # %".
    iPureIntro.
    intros t.
    destruct (decide (t = term)) as [-> | Hne]; last by rewrite lookup_insert_ne.
    rewrite lookup_insert.
    specialize (Hvp term).
    destruct (psb !! term) as [loglb |] eqn:Hloglb; rewrite Hlogn Hloglb /= in Hvp; last done.
    rewrite Hloglb /=.
    by trans logn.
  Qed.

End extend.

Lemma free_terms_inv_advance {nid ts tm} termc :
  gt_prev_term tm nid termc ->
  free_terms ts tm ->
  free_terms ts (<[nid := termc]> tm).
Proof.
  intros Hprev [Hdisj Hfree].
  split; first done.
  intros nidx t Ht t' Ht' Hlt.
  destruct (decide (nidx = nid)) as [-> | Hne]; last first.
  { rewrite lookup_insert_ne in Ht; last done.
    by specialize (Hfree _ _ Ht _ Ht' Hlt).
  }
  rewrite lookup_insert in Ht.
  symmetry in Ht. inv Ht.
  destruct Hprev as (termp & Htermp & Htermpc).
  assert (Hlt' : (termp < t')%nat) by lia.
  by specialize (Hfree _ _ Htermp _ Ht' Hlt').
Qed.

Section advance.
  Context `{!paxos_ghostG Σ}.

  Lemma paxos_inv_advance γ nids nid termc terml logn logn' :
    nid ∈ nids ->
    prefix_base_ledger γ termc logn' -∗
    prefix_growing_ledger γ termc logn' -∗
    own_current_term_half γ nid termc -∗
    own_ledger_term_half γ nid terml -∗
    own_node_ledger_half γ nid logn -∗
    paxos_inv γ nids ==∗
    own_current_term_half γ nid termc ∗
    own_ledger_term_half γ nid terml ∗
    own_node_ledger_half γ nid logn' ∗
    paxos_inv γ nids ∗
    is_accepted_proposal_lb γ nid termc logn'.
  Proof.
    iIntros (Hnid) "#Hpfb #Hpfg Htermc Hterml Hlogn Hinv".
    iNamed "Hinv".
    pose proof Hnid as Hterml.
    rewrite -Hdomtermlm elem_of_dom in Hterml.
    destruct Hterml as [terml' Hterml].
    iDestruct (big_sepM_delete _ _ nid with "Hnodes") as "[Hnode Hnodes]".
    { apply Hterml. }
  Qed.

End advance.

Section accept.
  Context `{!paxos_ghostG Σ}.

  Lemma paxos_inv_accept γ nids :
    paxos_inv γ nids ==∗
    paxos_inv γ nids.
  Proof.
  Qed.

End accept.
