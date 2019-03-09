From iris.bi Require Export bi.
From iris.bi Require Import tactics.
From iris.proofmode Require Export base environments classes modality_instances.
Import bi.
Import env_notations.

From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import base intro_patterns spec_patterns sel_patterns.
From iris.bi Require Export bi telescopes.
From stdpp Require Import namespaces.
From iris.proofmode Require Export classes notation tactics.
From stdpp Require Import hlist pretty.
Set Default Proof Using "Type".
Export ident.


Definition named_def {PROP: bi} (i: ident) (H: PROP) : PROP := H.
Definition named_aux {PROP: bi} : seal (@named_def PROP). by eexists. Qed.
Definition named {PROP: bi} := (@named_aux PROP).(unseal).
Definition named_eq {PROP : bi} := (@named_aux PROP).(seal_eq).

Fixpoint env_bundle_names {PROP: bi} (Γ: env PROP) : env PROP :=
  match Γ with
  | Enil => Enil
  | Esnoc Γ j x => Esnoc (env_bundle_names Γ) j (named j x)
  end.

Definition envs_bundle_names {PROP: bi} (Δ: envs PROP) : envs PROP :=
  let (Γp,Γs,n) := Δ in
  Envs Γp (env_bundle_names Γs) n.

Lemma envs_bundle_names_sound {PROP: bi} (Δ: envs PROP) :
  envs_bundle_names Δ = Δ.
Proof.
  destruct Δ as (Γp,Γs,p). rewrite /envs_bundle_names.
  f_equal.
  induction Γs; rewrite //= /named named_eq /named_def IHΓs //=.
Qed.

Lemma tac_bundle_names {PROP: bi} (Δ: envs PROP) Q :
  envs_entails (envs_bundle_names Δ) Q →
  envs_entails Δ Q.
Proof. by rewrite envs_entails_eq envs_bundle_names_sound. Qed.

Ltac bundle_names :=
  eapply tac_bundle_names;
  match goal with
    |- ?u =>
    let v := eval cbv [envs_bundle_names env_bundle_names] in u in change v
  end.

(* TODO: this is not very robust. *)
Ltac unbundle_names :=
  rewrite /named ?named_eq;
  match goal with |- ?u => let v := eval cbv [named_def] in u in change v end.

Ltac iAssignNames :=
  repeat match goal with
  | [ |- context[ environments.Esnoc _ (IAnon ?x) (named ?i _) ]] =>
      iRename (IAnon x) into i
      end; unbundle_names.

Tactic Notation "iNamed" tactic1(tac) :=
  bundle_names; tac; iAssignNames.

Ltac iDestructRep H :=
  let H1 := iFresh in
  let H2 := iFresh in
  let pat :=constr:(IList [cons (IIdent H1) (cons (IIdent H2) nil)]) in
  iDestruct H as pat; try (iDestructRep H1); try (iDestructRep H2);
  try (iDestruct H1 as "%"); try (iDestruct H2 as "%").

Ltac iDestructExRep H :=
  try (let H1 := iFresh in
       let H2 := iFresh in
       let pat := constr:(IList [cons (IIdent H1) (cons (IIdent H2) nil)]) in
       first [ (iDestruct H as (?) H; iDestructExRep H)
               || iDestruct H as pat; iDestructExRep H1; iDestructExRep H2;
               try (iDestruct H1 as "%"); try (iDestruct H2 as "%") ]).

Ltac iDestructRepR H :=
  let H2 := iFresh in
  let pat :=constr:(IList [cons (IAnom) (cons (IIdent H2) nil)]) in
  iDestruct H as pat; try (iDestructRepR H2).

Ltac iDestructIntro :=
  let H := iFresh in iIntros H; iDestructExRep H; iAssignNames.

Section test.
Context {PROP : bi}.
Context {P P' : PROP}.

Context (HPP': P ⊢ P').
Lemma HPP_named i : named i P ⊢ named i P'.
Proof using HPP'. by unbundle_names. Qed.

Lemma test Q : P ∗ Q ⊢ P' ∗ Q.
Proof using HPP'.
  iIntros "H".
  iDestruct "H" as "(HP&HQ)".
  iNamed (iPoseProof (HPP_named with "[$]") as "?").
  iFrame "HQ". iFrame "HP".
Qed.

Lemma test2 Q: (named "HP" P) ∗ (named "HQ" Q) ⊢ P ∗ Q.
Proof using HPP'.
  iDestructIntro. iFrame "HP". iFrame "HQ".
Qed.

End test.