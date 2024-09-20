From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import quorum.

Definition ledger := list string.

Definition proposals := gmap nat ledger.

Inductive nodedec :=
| Accept (v : ledger)
| Reject.

Definition ballot := gmap nat nodedec.

Section def.
  Context `{Countable A}.
  (* XXX: fix the naming scheme *)
  Implicit Type t n : nat.
  Implicit Type l : proposals.
  Implicit Type v : ledger.
  Implicit Type bs bsq : gmap A proposals.
  Implicit Type ps psb : proposals.

  Definition accepted_in l t v :=
    ∃ v', l !! t = Some v' ∧ prefix v v'.

  Definition chosen_in bs t v :=
    ∃ bsq, bsq ⊆ bs ∧
           cquorum_size (dom bs) (dom bsq) ∧
           map_Forall (λ _ l, accepted_in l t v) bsq.

  Definition chosen bs v :=
    ∃ t, chosen_in bs t v.

  Definition consistency bs :=
    ∀ v1 v2, chosen bs v1 -> chosen bs v2 -> prefix v1 v2 ∨ prefix v2 v1.

  Definition proposed_after_chosen bs ps :=
    ∀ t1 t2 v1 v2,
    (t1 < t2)%nat ->
    chosen_in bs t1 v1 ->
    ps !! t2 = Some v2 ->
    prefix v1 v2.

  (* Compute the latest term in which a proposal is accepted before [n]. *)
  Fixpoint latest_term_before_with `{Lookup nat B M}
    (f : option B -> option ledger) (t : nat) (m : M) :=
    match t with
    | O => O
    | S p => match f (m !! p) with
            | Some _ => p
            | _ => latest_term_before_with f p m
            end
    end.

  Definition latest_term_before t ps :=
    latest_term_before_with id t ps.

  Definition latest_term_before_quorum_step (x : A) (cur prev : nat) : nat :=
    cur `max` prev.

  Definition latest_term_before_quorum_with `{Lookup nat B M}
    (f : option B -> option ledger) (ms : gmap A M) (t : nat) :=
    let ts := fmap (latest_term_before_with f t) ms in
    map_fold latest_term_before_quorum_step O ts.

  Definition longest_proposal_step (x : A) (cur prev : option ledger) :=
    match prev with
    | None => cur
    | Some lprev => match cur with
                   | Some lcur => if decide (length lprev < length lcur)%nat
                                 then cur
                                 else prev
                   | _ => prev
                   end
    end.

  Definition longest_proposal ovs :=
    map_fold longest_proposal_step None ovs.

  Definition ledger_at_term_with `{Lookup nat B M}
    (f : option B -> option ledger) (t : nat) (m : M) := f (m !! t).

  Definition longest_proposal_in_term_with `{Lookup nat B M}
    (f : option B -> option ledger) (ms : gmap A M) t :=
    let ovs := fmap (ledger_at_term_with f t) ms in
    longest_proposal ovs.

  Definition equal_latest_longest_proposal_with `{Lookup nat B M}
    (f : option B -> option ledger) (ms : gmap A M) t v :=
    let t' := latest_term_before_quorum_with f ms t in
    longest_proposal_in_term_with f ms t' = Some v.

  Definition equal_latest_longest_proposal bsq t v :=
    equal_latest_longest_proposal_with id bsq t v.

  Definition valid_base_proposal bs t v :=
    ∃ bsq : gmap A proposals,
      bsq ⊆ bs ∧
      cquorum_size (dom bs) (dom bsq) ∧
      equal_latest_longest_proposal bsq t v.

  Definition valid_base_proposals bs psb :=
    map_Forall (λ n v, valid_base_proposal bs n v) psb.

  Definition valid_lb_ballot psb l :=
    ∀ t v, l !! t = Some v -> ∃ v', psb !! t = Some v' ∧ prefix v' v.

  Definition valid_lb_ballots bs psb :=
    map_Forall (λ _ l, valid_lb_ballot psb l) bs.

  Definition valid_ub_ballot ps l :=
    ∀ t v, l !! t = Some v -> ∃ v', ps !! t = Some v' ∧ prefix v v'.

  Definition valid_ub_ballots bs ps :=
    map_Forall (λ _ l, valid_ub_ballot ps l) bs.

  Definition valid_proposals ps psb :=
    map_Forall2 (λ _ (lb l : ledger), prefix lb l) psb ps.

  Definition free_term_with_partf (P : A -> nat -> Prop) (ts : gset nat) (x : A) (t : nat) :=
    ∀ t', P x t' -> (t < t')%nat -> t' ∉ ts.

  Definition free_terms_with_partf (P : A -> nat -> Prop) (ts : gset nat) (tm : gmap A nat) :=
    (∀ x1 x2 t, x1 ≠ x2 -> P x1 t -> not (P x2 t)) ∧
    map_Forall (λ x n, free_term_with_partf P ts x n) tm.

End def.

Definition max_nodes : Z := 16.

Definition is_term_of_node (x : u64) (t : nat) :=
  t `mod` max_nodes = (uint.Z x).

Lemma is_term_of_node_partitioned x1 x2 t :
  x1 ≠ x2 -> is_term_of_node x1 t -> not (is_term_of_node x2 t).
Proof.
  unfold is_term_of_node.
  intros Hne Hx1.
  rewrite Hx1.
  by apply word.unsigned_inj'.
Qed.

Definition free_terms ts tm :=
  free_terms_with_partf is_term_of_node ts tm.

Class paxos_ghostG (Σ : gFunctors).

Record paxos_names := {}.
