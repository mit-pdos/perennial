From iris.proofmode Require Export tactics.
From iris.proofmode Require Import reduction coq_tactics intro_patterns.

From iris_string_ident Require Export ltac2_string_ident.

Tactic Notation "iApply" open_constr(lem) "in" constr(i) :=
  iDestruct (lem with i) as i.

Lemma tac_assumption_eq {PROP:bi} Δ i p (P Q: PROP) :
  envs_lookup i Δ = Some (p, P) →
  P = Q →
  (let Δ' := envs_delete true i p Δ in
   if env_spatial_is_nil Δ' then TCTrue
   else TCOr (Absorbing Q) (AffineEnv (env_spatial Δ'))) →
  envs_entails Δ Q.
Proof.
  intros ? -> ?.
  eapply coq_tactics.tac_assumption; eauto.
  apply _.
Qed.

Tactic Notation "iExactEq" constr(H) :=
  let i := lazymatch type of H with
           | string => constr:(INamed H)
           | _ => H
           end in
  eapply (tac_assumption_eq _ i);
  [ first [ pm_reflexivity
          | fail 1 "iExactEq:" H "not found" ]
  | (* equality goal *)
  | pm_reduce; iSolveTC
  ].

(* TODO: this works, but maybe we can do better *)
Tactic Notation "iLeft" "in" constr(H) :=
  let pat := constr:(IList [[IIdent H; IDrop]]) in
  iDestruct H as pat.
Tactic Notation "iRight" "in" constr(H) :=
  let pat := constr:(IList [[IDrop; IIdent H]]) in
  iDestruct H as pat.

Module tests.
  Section bi.
    Context {PROP: bi} `{BiAffine PROP}.
    Set Default Proof Using "All".
    Implicit Types (P Q: PROP) (Φ: nat → PROP).

    Example test_simple P : P -∗ P.
    Proof.
      iIntros "H".
      iExactEq "H".
      reflexivity.
    Qed.

    Example test_predicate Φ n : Φ (n + 1) -∗ Φ (S n).
    Proof.
      iIntros "H".
      iExactEq "H".
      f_equal; lia.
    Qed.

    Example test_non_existent P : P -∗ P.
    Proof.
      iIntros "H".
      Fail iExactEq "foo".
    Abort.
  End bi.
End tests.
