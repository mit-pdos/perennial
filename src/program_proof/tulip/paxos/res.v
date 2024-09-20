From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import quorum extend list.
From Perennial.program_proof.tulip.paxos Require Import base.

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

    Lemma internal_log_witness {γ l} :
      own_internal_log γ l -∗
      is_internal_log_lb γ l.
    Admitted.

    Lemma internal_log_prefix {γ l lb} :
      own_internal_log γ l -∗
      is_internal_log_lb γ lb -∗
      ⌜prefix lb l⌝.
    Admitted.

  End internal_log.

  Section proposal.

    (** Elements. *)

    Definition own_proposals γ (vs : proposals) : iProp Σ.
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

    Lemma proposal_insert {γ vs} t v :
      vs !! t = None ->
      own_proposals γ vs ==∗
      own_proposals γ (<[t := v]> vs) ∗ own_proposal γ t v.
    Admitted.

    Lemma proposal_lookup {γ vs t v} :
      own_proposal γ t v -∗
      own_proposals γ vs -∗
      ⌜vs !! t = Some v⌝.
    Admitted.

    Lemma proposal_update {γ vs t v1} v2 :
      prefix v1 v2 ->
      own_proposal γ t v1 -∗
      own_proposals γ vs ==∗
      own_proposal γ t v2 ∗ own_proposals γ (<[t := v2]> vs).
    Admitted.

    Lemma proposal_witness {γ t v} :
      own_proposal γ t v -∗
      is_proposal_lb γ t v.
    Admitted.

    Lemma proposal_prefix {γ t vlb v} :
      is_proposal_lb γ t vlb -∗
      own_proposal γ t v -∗
      ⌜prefix vlb v⌝.
    Admitted.

  End proposal.

  Section base_proposal.

    (** Elements. *)

    Definition own_base_proposals γ (vs : proposals) : iProp Σ.
    Admitted.

    Definition is_base_proposal_receipt γ (t : nat) (v : ledger) : iProp Σ.
    Admitted.

    (** Type class instances. *)

    #[global]
    Instance is_base_proposal_receipt_persistent γ t v :
      Persistent (is_base_proposal_receipt γ t v).
    Admitted.

    (** Rules. *)

    Lemma base_proposal_insert {γ vs} t v :
      vs !! t = None ->
      own_base_proposals γ vs ==∗
      own_base_proposals γ (<[t := v]> vs) ∗ is_base_proposal_receipt γ t v.
    Admitted.

    Lemma base_proposal_lookup {γ vs t v} :
      is_base_proposal_receipt γ t v -∗
      own_base_proposals γ vs -∗
      ⌜vs !! t = Some v⌝.
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

    Definition own_accepted_proposals γ (nid : u64) (vs : proposals) : iProp Σ.
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

    Lemma accepted_proposal_insert {γ nid vs t v} :
      vs !! t = None ->
      own_accepted_proposals γ nid vs ==∗
      own_accepted_proposals γ nid (<[t := v]> vs) ∗ own_accepted_proposal γ nid t v.
    Admitted.

    Lemma accepted_proposal_update {γ nid vs t v1} v2 :
      prefix v1 v2 ->
      own_accepted_proposal γ nid t v1 -∗
      own_accepted_proposals γ nid vs ==∗
      own_accepted_proposal γ nid t v2 ∗ own_accepted_proposals γ t (<[t := v2]> vs).
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

  Definition node_inv γ nid terml : iProp Σ :=
    ∃ ds psa termc logn,
      "Hpastd" ∷ own_past_nodedecs γ nid ds ∗
      "Hpsa"   ∷ own_accepted_proposals γ nid psa ∗
      "Htermc" ∷ own_current_term_half γ nid termc ∗
      "Hterml" ∷ own_ledger_term_half γ nid terml ∗
      "Hlogn"  ∷ own_node_ledger_half γ nid logn ∗
      "%Hfixed"  ∷ ⌜fixed_proposals ds psa⌝ ∗
      "%Hdompsa" ∷ ⌜free_terms_after terml (dom psa)⌝ ∗
      "%Hlogn"   ∷ ⌜psa !! terml = Some logn⌝ ∗
      "%Hlends"  ∷ ⌜length ds = termc⌝ ∗
      "%Htermlc" ∷ ⌜(terml ≤ termc)%nat⌝.

  Definition prefix_of_accepted_proposal γ nid t logi: iProp Σ :=
    ∃ loga,
      "#Hloga"   ∷ is_accepted_proposal_lb γ nid t loga ∗
      "%Hprefix" ∷ ⌜prefix logi loga⌝.

  Definition safe_internal_log γ nids logi : iProp Σ :=
    ∃ nidsq t,
      "#Hacpt"   ∷ ([∗ set] nid ∈ nidsq, prefix_of_accepted_proposal γ nid t logi) ∗
      "%Hquorum" ∷ ⌜cquorum_size nids nidsq⌝.

  Definition equal_latest_longest_proposal_nodedec (dsq : gmap u64 (list nodedec)) t v :=
    equal_latest_longest_proposal_with (mbind nodedec_to_ledger) dsq t v.

  Definition safe_base_proposal γ nids t v : iProp Σ :=
    ∃ dssq,
      "#Hdsq"    ∷ ([∗ map] nid ↦ ds ∈ dssq, is_past_nodedecs_lb γ nid ds) ∗
      "%Hlen"    ∷ ⌜map_Forall (λ _ ds, (t ≤ length ds)%nat) dssq⌝ ∗
      "%Hincl"   ∷ ⌜dom dssq ⊆ nids⌝ ∗
      "%Hquorum" ∷ ⌜cquorum_size nids (dom dssq)⌝ ∗
      "%Heq"     ∷ ⌜equal_latest_longest_proposal_nodedec dssq t v⌝.

  Definition latest_term_before_nodedec t (ds : list nodedec) :=
    latest_term_before_with (mbind nodedec_to_ledger) t ds.

  Definition latest_term_nodedec ds :=
    latest_term_before_nodedec (length ds) ds.

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
      "#Hsafelogi"  ∷ safe_internal_log γ nids logi ∗
      "#Hsafepsb"   ∷ ([∗ map] t ↦ v ∈ psb, safe_base_proposal γ nids t v) ∗
      "%Hbase"      ∷ ⌜map_Forall2 (λ _ (vlb v : ledger), prefix vlb v) psb ps⌝ ∗
      "%Hdomtermlm" ∷ ⌜dom termlm = nids⌝ ∗
      "%Hdompsb"    ∷ ⌜free_terms (dom psb) termlm⌝.

  #[global]
  Instance paxos_inv_timeless γ nids :
    Timeless (paxos_inv γ nids).
  Admitted.

  Definition know_paxos_inv γ nids : iProp Σ :=
    inv paxosNS (paxos_inv γ nids).

End inv.

(**
 * Notes on state-machine actions of Paxos:
 * - ascend(t, v): insert [(t, v)] into [proposals] and [base_proposals].
 * - extend(t, v): update [proposals !! t] to [v]
 * - prepare(t): snoc [accepted_proposals !! (length ballot)] to [ballot] if it exists, and extend [ballot] with [Reject] up to [t].
 * - accept(t, v): insert/update [(t, v)] to [accepted_proposals].
 * - commit(v): update [internal_log] to [v].
 *)

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

  Lemma latest_term_before_nodedec_append t ds dsapp :
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
    by apply latest_term_before_nodedec_append.
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

  Lemma fixed_proposals_latest_term_before_nodedec ds psa t :
    (t ≤ length ds)%nat ->
    fixed_proposals ds psa ->
    latest_term_before_nodedec t ds = latest_term_before t psa.
  Proof.
    intros Hlen Hfixed.
    rewrite /latest_term_before_nodedec /latest_term_before /=.
    induction t as [| p IH]; first done.
    simpl.
    assert (p < length ds)%nat as Hp by lia.
    apply list_lookup_lt in Hp as [d Hd].
    specialize (Hfixed _ _ Hd).
    rewrite Hd /= -Hfixed IH; [done | lia].
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
    destruct (decide (terml = termc)) as [-> | Hne]; last first.
    { (* Case: [terml < termc] iff no ledger accepted at [termc] yet. *)
      (* Update the current term [termc] to [termc']. *)
      iMod (current_term_update termc' with "HtermcX Htermc") as "[HtermcX Htermc]".
      (* Extend the node decisions [d] with [Reject]. *)
      set ds' := extend termc' Reject ds.
      iMod (past_nodedecs_update ds' with "Hpastd") as "Hpastd".
      { apply extend_prefix. }
      (* Extract a witness of the extended past decision. *)
      iDestruct (past_nodedecs_witness with "Hpastd") as "#Hdlb".
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
        rewrite Hfixed in Hlogn.
        apply nodedec_to_ledger_Some_inv in Hlogn.
        by rewrite Hlogn.
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
    iMod (past_nodedecs_update ds' with "Hpastd") as "Hpastd".
    { etrans; last apply extend_prefix.
      by apply prefix_app_r.
    }
    (* Extract a witness of the extended past decision. *)
    iDestruct (past_nodedecs_witness with "Hpastd") as "#Hdlb".
    unshelve epose proof
      (fixed_proposals_inv_prepare_term_eq _ _ _ _ _ Hlends Hlt Hlogn Hdompsa Hfixed) as Hfixed'.
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

  Lemma own_ledger_term_node_inv_eq γ nid terml terml' :
    own_ledger_term_half γ nid terml -∗
    node_inv γ nid terml' -∗
    ⌜terml' = terml⌝.
  Proof.
    iIntros "HtermlX Hnode".
    iNamed "Hnode".
    by iDestruct (ledger_term_agree with "HtermlX Hterml") as %->.
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
    iDestruct (own_ledger_term_node_inv_eq with "Hterml Hnode") as %->.
    iMod (node_inv_prepare _ _ _ _ _ _ Hlt with "Htermc Hv Hnode")
      as "(Htermc & Hv & Hnode & #Hpast)".
    iDestruct ("HnodesC" with "Hnode") as "Hnodes".
    by iFrame "∗ # %".
  Qed.

End prepare.
