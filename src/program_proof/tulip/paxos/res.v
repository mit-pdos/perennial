From Perennial.program_proof Require Import grove_prelude.
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

(**
 * Notes on state-machine actions of Paxos:
 * - ascend(t, v): insert [(t, v)] into [proposals] and [base_proposals].
 * - extend(t, v): update [proposals !! t] to [v]
 * - prepare(t): snoc [accepted_proposals !! (length ballot)] to [ballot] if it exists, and extend [ballot] with [Reject] up to [t].
 * - advance(t, v): insert [(t, v)] into [accepted_proposals].
 * - accept(t, v): update [accepted_proposals !! t] to [v].
 * - commit(v): update [internal_log] to [v].
 *)
