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

(** freezing: hiding a hypothesis body

    the basic interface for this trick is borrowed from VST *)

Definition freeze {A} (x:A) := x.

Lemma freeze_eq {A} (x:A) : freeze x = x.
Proof. reflexivity. Qed.

Ltac iFreeze H :=
  let i := lazymatch type of H with
           | string => constr:(INamed H)
           | _ => H
           end in
  lazymatch iTypeOf i with
  | Some (_, ?P) =>
    iEval (rewrite -(freeze_eq P)) in i;
    let var := fresh "__frozen" in
    set (var:=freeze P)
  | None => let H := pretty_ident i in
            fail 1 "iFreeze:" H "not found"
  end.

Ltac iThaw H :=
  let i := lazymatch type of H with
           | string => constr:(INamed H)
           | _ => H
           end in
  lazymatch iTypeOf i with
  | Some (_, ?P) =>
    first [ is_var P; subst P; rewrite freeze_eq
          | let H := pretty_ident i in
            fail 1 "iThaw:" H "is not frozen"]
  | None => let H := pretty_ident i in
            fail 1 "iThaw:" H "not found"
  end.

Typeclasses Opaque freeze.
Opaque freeze.

(* hide frozen terms from display (even in the Coq context) *)
(* closing this scope will re-display frozen terms *)
Declare Scope freeze_scope.
Notation "☃" := (freeze _) (at level 0, only printing) : freeze_scope.
Global Open Scope freeze_scope.

Lemma tac_delay_split {PROP: bi} (R P Q: PROP) :
  (P ∗ R) -∗ (R -∗ Q) -∗ P ∗ Q.
Proof.
  iIntros "[$ R]".
  iIntros "H".
  iApply "H"; iFrame.
Qed.

Ltac iSplitDelay :=
  let PROP := iBiOfGoal in
  let R := fresh "remainder" in
  evar (R:PROP.(bi_car));
  iApply (tac_delay_split R with "[-] []");
  subst R.

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

    Example test_freeze Φ n :
      Φ (n + 1) -∗ True.
    Proof.
      iIntros "H".
      iFreeze "H".
      iThaw "H".
      auto.
    Qed.

    Example test_delay_split (P Q R S T: PROP) :
      P ∗ Q ∗ R ∗ S ∗ T -∗ (P ∗ T ∗ R) ∗ (S ∗ Q).
    Proof.
      iIntros "(P&Q&R&S&T)".
      iSplitDelay.
      - iFrame.
        rewrite left_id. iAccu. (* would be iNamedAccu *)
      - iIntros "(Q&S)". (* would be iNamed 1 *)
        iFrame.
    Qed.

  End bi.
End tests.
