Require Import Tactical.Propositional.
Require Import Helpers.RelationAlgebra.

Import RelationNotations.

Ltac rel_congruence :=
  let solver := try reflexivity in
  match goal with
  (* monotonicity over rimpl *)
  | |- rimpl (and_then _ ?rx) (and_then _ ?rx) =>
    apply and_then_monotonic_r; intros;
    solver
  | |- rimpl (and_then _ _) (and_then _ _) =>
    apply and_then_monotonic; intros;
    solver
  | |- rimpl (seq_star _) (seq_star _) =>
    apply star_monotonic;
    solver

  (* congruence over requiv *)
  | |- requiv (and_then _ ?rx) (and_then _ ?rx) =>
    apply and_then_cong_l; intros;
    solver
  | |- requiv (and_then ?p _) (and_then ?p _) =>
    apply and_then_cong_r; intros;
    solver
  | |- requiv (and_then _ _) (and_then _ _) =>
    apply and_then_equiv_cong; intros;
    solver
  | |- requiv (seq_star _) (seq_star _) =>
    apply star_congruent;
    solver
  | |- requiv (bind_star _ ?v) (bind_star _ ?v) =>
    apply bind_star_congruent; intros
  end.

Ltac setoid_norm_goal :=
  match goal with
  | |- context[and_then (and_then _ _) _] =>
    setoid_rewrite bind_assoc
  | |- context[and_then (pure _) _] =>
    setoid_rewrite bind_left_id
  | |- context[@identity _ unit] =>
    setoid_rewrite unit_identity
  | |- context[rel_or _ (rel_or _ _)] =>
    setoid_rewrite rel_or_assoc
  | |- context[and_then (none) _] =>
    setoid_rewrite none_absorb_l
  | |- context[and_then _ (fun _ => none)] =>
    setoid_rewrite none_absorb_r
  end.

Ltac setoid_norm_hyp H :=
  match type of H with
  | context[and_then (and_then _ _) _] =>
    setoid_rewrite bind_assoc in H
  | context[and_then (pure _) _] =>
    setoid_rewrite bind_left_id in H
  | context[@identity _ unit] =>
    setoid_rewrite unit_identity in H
  | context[rel_or _ (rel_or _ _)] =>
    setoid_rewrite rel_or_assoc in H
  end.

Ltac setoid_norm_hyps :=
  match goal with
  | [ H: context[and_then (and_then _ _) _] |- _ ] =>
    setoid_rewrite bind_assoc in H
  | [ H: context[and_then (pure _) _] |- _ ] =>
    setoid_rewrite bind_left_id in H
  | [ H: context[@identity _ unit] |- _ ] =>
    setoid_rewrite unit_identity in H
  | [ H: context[rel_or _ (rel_or _ _)] |- _ ] =>
    setoid_rewrite rel_or_assoc in H
  end.

Ltac norm_goal :=
  repeat setoid_norm_goal.

Ltac norm_hyp H :=
  repeat (setoid_norm_hyp H).

Ltac norm_all :=
  repeat (setoid_norm_goal || setoid_norm_hyps).

Tactic Notation "norm" := norm_goal; try reflexivity.
Tactic Notation "norm" "in" "*" := norm_all; try reflexivity.
Tactic Notation "norm" "in" ident(H) := norm_hyp H.

(* attempt to make rewriting across monad associativity a bit easier; instead
     of massaging the goal to have [r1] appear, instead generalize the
     hypothesis to apply to apply to [forall rx, r1; rx] *)
Lemma rimpl_rx A B T (r1 r2: relation A B T) :
  r1 ---> r2 ->
  (forall C T2 (rx: T -> relation B C T2),
      and_then r1 rx ---> and_then r2 rx).
Proof.
  intros.
  rel_congruence; auto.
Qed.

Create HintDb relation_rewriting.

Local Ltac with_hyp H tac :=
  let H' := fresh "Htmp" in
  pose proof H as H';
  tac H';
  clear H'.

Ltac rel_hyp H tac :=
  (with_hyp H ltac:(fun H => autounfold with relation_rewriting in H;
                          tac H));
  norm.

Tactic Notation "rel" "with" constr(H) tactic(t) := rel_hyp H t.

Tactic Notation "rew" constr(pf) :=
  rel_hyp pf ltac:(fun H => setoid_rewrite -> H).
Tactic Notation "rew<-" constr(pf) :=
  rel_hyp pf ltac:(fun H => setoid_rewrite <- H).
Tactic Notation "rew" "->" uconstr(pf) "in" ident(H) :=
  rel_hyp pf ltac:(fun H' => setoid_rewrite -> H' in H at 1; norm_hyp H).
Tactic Notation "rew" "<-" uconstr(pf) "in" ident(H) :=
  rel_hyp pf ltac:(fun H' => setoid_rewrite <- H' in H at 1; norm_hyp H).

Ltac Split := match goal with
              | |- _ + _ ---> _ =>
                apply rel_or_elim; norm
              | |- and_then (_ + _) _ ---> _ =>
                apply rel_or_elim_rx; norm
              | |- ?g ---> _ =>
                match g with
                | context[_ + _] =>
                  etransitivity; [
                    repeat (setoid_rewrite bind_dist_l ||
                            setoid_rewrite bind_dist_r);
                    apply rel_or_elim; norm_goal |
                    reflexivity ]
                end
              end.

Ltac Left := match goal with
             | |- _ ---> ?g =>
               match g with
               | context[_ + _] =>
                 etransitivity;
                 [ | rewrite <- rel_or_introl; norm_goal ];
                 [ reflexivity | ];
                 try reflexivity
               end
             end.

Ltac Right := match goal with
              | |- _ ---> ?g =>
                match g with
                | context[_ + _] =>
                 etransitivity;
                 [ | rewrite <- rel_or_intror; norm_goal ];
                 [ reflexivity | ];
                 try reflexivity
                end
              end.

Ltac left_associate H :=
  repeat setoid_rewrite <- bind_assoc;
  try repeat setoid_rewrite <- bind_assoc in H.

Local Ltac left_assoc_rel_hyp H tac :=
  rel_hyp H ltac:(fun H => left_associate H;
                        tac H).

Tactic Notation "left_assoc" "with" constr(H) tactic(t) :=
  left_assoc_rel_hyp H t.

Tactic Notation "left_assoc" "rew" constr(H) :=
  left_assoc_rel_hyp H ltac:(fun H => setoid_rewrite H).

Tactic Notation "left_assoc" "rew" "<-" constr(H) :=
  left_assoc_rel_hyp H ltac:(fun H => setoid_rewrite <- H).
