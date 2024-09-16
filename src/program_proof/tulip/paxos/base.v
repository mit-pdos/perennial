From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import quorum.

Definition ledger := list string.

Definition proposals := gmap nat ledger.

Inductive nodedec :=
| Accept (v : ledger)
| Reject.

Definition ballot := list nodedec.

Section def.
  Context `{Countable A}.
  Implicit Type t n : nat.
  Implicit Type l : ballot.
  Implicit Type v : ledger.
  Implicit Type bs bsq : gmap A ballot.
  Implicit Type ps psb : proposals.

  Definition accepted_in l t v :=
    ∃ v', l !! t = Some (Accept v') ∧ prefix v v'.

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
  Fixpoint latest_term_before t l : nat :=
    match t with
    | O => O
    | S p => match l !! p with
            | Some d => match d with
                       | Accept _ => p
                       | Reject => latest_term_before p l
                       end
            | _ => latest_term_before p l
            end
    end.

  (* Definition latest_term (l : ballot) := latest_before (length l) l. *)

  Definition latest_term_before_quorum_step (x : A) (cur prev : nat) : nat :=
    cur `max` prev.

  Definition latest_term_before_quorum bsq t :=
    let ts := fmap (latest_term_before t) bsq in
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

  Definition longest_proposal_in_term bsq t :=
    let ovs := fmap (λ l, match l !! t with
                          | Some (Accept v) => Some v
                          | _ => None
                          end) bsq in
    longest_proposal ovs.

  Definition equal_latest_longest_proposal bsq psb t v :=
    let t' := latest_term_before_quorum bsq t in
    longest_proposal_in_term bsq t' = Some v.

  Definition valid_base_proposal bs psb t v :=
    ∃ bsq : gmap A ballot,
      bsq ⊆ bs ∧
      cquorum_size (dom bs) (dom bsq) ∧
      equal_latest_longest_proposal bsq psb t v.

  Definition valid_base_proposals bs psb :=
    map_Forall (λ n v, valid_base_proposal bs psb n v) psb.

  Definition valid_lb_ballot psb l :=
    ∀ t v, l !! t = Some (Accept v) -> ∃ v', psb !! t = Some v' ∧ prefix v' v.

  Definition valid_lb_ballots bs psb :=
    map_Forall (λ _ l, valid_lb_ballot psb l) bs.

  Definition valid_ub_ballot ps l :=
    ∀ t v, l !! t = Some (Accept v) -> ∃ v', ps !! t = Some v' ∧ prefix v v'.

  Definition valid_ub_ballots bs ps :=
    map_Forall (λ _ l, valid_ub_ballot ps l) bs.

  Definition valid_proposals ps psb :=
    map_Forall2 (λ _ (lb l : ledger), prefix lb l) psb ps.

End def.

Class paxos_ghostG (Σ : gFunctors).

Record paxos_names := {}.
