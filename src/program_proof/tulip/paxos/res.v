From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import quorum.
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

    Lemma past_nodedecs_update γ nid d1 d2 :
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

  Definition fixed_proposals (ds : list nodedec) (ps : proposals) :=
    ∀ t od, ds !! t = od ->
            match od with
            | Some (Accept v) => ps !! t = Some v
            | Some Reject => ps !! t = None
            | _ => True
            end.

  Definition free_terms_after (t : nat) (ts : gset nat) :=
    ∀ t', (t < t')%nat -> t' ∉ ts.


  Definition node_inv γ nid terml : iProp Σ :=
    ∃ ds psa termc logn,
      "Hblt"   ∷ own_past_nodedecs γ nid ds ∗
      "Hpsa"   ∷ own_accepted_proposals γ nid psa ∗
      "Htermc" ∷ own_current_term_half γ nid termc ∗
      "Hterml" ∷ own_ledger_term_half γ nid terml ∗
      "Hlogn"  ∷ own_node_ledger_half γ nid logn ∗
      "%Hfixed"  ∷ ⌜fixed_proposals ds psa⌝ ∗
      "%Hdompsa" ∷ ⌜free_terms_after terml (dom psa)⌝ ∗
      "%Hlogn"   ∷ ⌜psa !! terml = Some logn⌝ ∗
      "%Hlenblt" ∷ ⌜length ds = termc⌝ ∗
      "%Htermlc" ∷ ⌜(terml ≤ termc)%nat⌝ ∗
      "%Hlatest" ∷ ⌜terml ≠ termc -> latest_term_before termc ds = terml⌝.

  Definition prefix_of_accepted_proposal γ nid t logi: iProp Σ :=
    ∃ loga,
      "#Hloga"   ∷ is_accepted_proposal_lb γ nid t loga ∗
      "%Hprefix" ∷ ⌜prefix logi loga⌝.

  Definition safe_internal_log γ nids logi : iProp Σ :=
    ∃ nidsq t,
      "#Hacpt"   ∷ ([∗ set] nid ∈ nidsq, prefix_of_accepted_proposal γ nid t logi) ∗
      "%Hquorum" ∷ ⌜cquorum_size nids nidsq⌝.

  Definition safe_base_proposal γ nids t v : iProp Σ :=
    ∃ dsq,
      "#Hdsq"    ∷ ([∗ map] nid ↦ d ∈ dsq, is_past_nodedecs_lb γ nid d) ∗
      "%Hlen"    ∷ ⌜map_Forall (λ _ d, (t ≤ length d)%nat) dsq⌝ ∗
      "%Hincl"   ∷ ⌜dom dsq ⊆ nids⌝ ∗
      "%Hquorum" ∷ ⌜cquorum_size nids (dom dsq)⌝ ∗
      "%Heq"     ∷ ⌜equal_latest_longest_proposal dsq t v⌝.

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
      "#Hsafelogi" ∷ safe_internal_log γ nids logi ∗
      "#Hsafepsb"  ∷ ([∗ map] t ↦ v ∈ psb, safe_base_proposal γ nids t v) ∗
      "%Hbase"     ∷ ⌜map_Forall2 (λ _ (vlb v : ledger), prefix vlb v) psb ps⌝ ∗
      "%Hdompsb"   ∷ ⌜free_terms (dom psb) termlm⌝.

  #[global]
  Instance paxos_inv_timeless γ nids :
    Timeless (paxos_inv γ nids).
  Admitted.

  Definition know_paxos_inv γ nids : iProp Σ :=
    inv paxosNS (paxos_inv γ nids).

End inv.

(**
 * Notes on state-machine actions of Paxos:
 * - nominate(termc)
 * - ascend(t, v): insert [(t, v)] into [proposals] and [base_proposals].
 * - extend(t, v): update [proposals !! t] to [v]
 * - prepare(t): snoc [accepted_proposals !! (length ballot)] to [ballot] if it exists, and extend [ballot] with [Reject] up to [t].
 * - accept(t, v): same as prepare(t), but additionally insert/update [(t, v)] to [accepted_proposals].
 * - commit(v): update [internal_log] to [v].
 *)

Section invariance.
  Context `{!paxos_ghostG Σ}.

  Lemma paxos_inv_nominate γ nids nid termc termc' :
    own_current_term_half γ nid termc -∗
    paxos_inv γ nids ==∗
    own_current_term_half γ nid termc' ∗
    paxos_inv γ nids.
  Admitted.

End invariance.
