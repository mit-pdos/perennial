
From iris.algebra Require Export auth functions csum.
Require Export CSL.WeakestPre CSL.Lifting CSL.Counting.
Require Import Helpers.RelationTheorems.
From iris.proofmode Require Export tactics.
From RecoveryRefinement Require Export Lib.

From iris.bi Require Export bi.
From iris.bi Require Import tactics.
From iris.proofmode Require Export base environments classes modality_instances.
Set Default Proof Using "Type".
Import bi.
Import env_notations.

From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import base intro_patterns spec_patterns sel_patterns.
From iris.bi Require Export bi telescopes.
From stdpp Require Import namespaces.
From iris.proofmode Require Export classes notation.
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
  of_envs Δ -∗ of_envs (envs_bundle_names Δ).
Proof.
  destruct Δ as (Γp,Γs,p). rewrite /of_envs.
  induction Γs.
  rewrite //=.
  iIntros "(%&?&?)".
  admit.
Admitted.

Lemma tac_bundle_names {PROP: bi} (Δ: envs PROP) Q :
  envs_entails (envs_bundle_names Δ) Q →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq.
  by rewrite -envs_bundle_names_sound.
Qed.

Ltac bundle_names :=
  match goal with
    |- ?u =>
    let v := eval cbv [envs_bundle_names env_bundle_names] in u in change v
  end.

Ltac unbundle_names :=
  rewrite /named ?named_eq;
  match goal with |- ?u => let v := eval cbv [named_def] in u in change v end.

(*
Class NamedFrame {PROP : bi} (i: ident) (p : bool) (R P Q : PROP) :=
  nframe : □?p R ∗ Q ⊢ P.
Arguments NamedFrame {_} _ _ _%I _%I _%I.
Arguments nframe {_ _ _} _%I _%I _%I {_}.
Hint Mode NamedFrame + + + ! ! - : typeclass_instances.

Global Instance FrameNamedFrame {PROP: bi} (i: ident) (p: bool) (R P Q: PROP):
  Frame p R P Q → NamedFrame i p R (named i P) Q.
Proof. rewrite /Frame/NamedFrame/named named_eq//=. Qed.
*)

Section test.
Context {PROP : bi}.
Lemma test (P Q: PROP) : P ∗ Q ⊢ P ∗ Q.
Proof. iIntros "H". iDestruct "H" as "(HP&HQ)". eapply tac_bundle_names; bundle_names.

  evar (i: ident).
  let i' := eval unfold i in i in
  iAssert (named i' P) with "[$]" as "?".
  repeat match goal with
  | [ |- context[ environments.Esnoc _ ?x (named ?i _) ]] =>
      iRename x into i
      end.
  unbundle_names.
  iFrame.
Qed.

(*
Local Ltac iFrameFinish :=
  pm_prettify;
  try match goal with
  | |- envs_entails _ True => by iPureIntro
  | |- envs_entails _ emp => iEmpIntro
  end.
Lemma tac_frame Δ Δ' i p (R P Q: PROP) :
  envs_lookup_delete false i Δ = Some (p, R, Δ') →
  NamedFrame i p R P Q →
  envs_entails Δ' Q → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq. intros [? ->]%envs_lookup_delete_Some ? HQ.
  rewrite (envs_lookup_sound' _ false) //. by rewrite -(nframe R P) HQ.
Qed.
Print envs.

Local Ltac iFrameHyp H :=
  iStartProof; idtac H;
  eapply tac_frame with _ H _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iFrame:" H "not found"
    |iSolveTC ||
     let R := match goal with |- NamedFrame _ _ ?R _ _ => R end in
     fail "iFrame: cannot frame" R
    |iFrameFinish].

Local Ltac iFramePure t :=
  iStartProof;
  let φ := type of t in
  eapply (tac_frame_pure _ _ _ _ t);
    [iSolveTC || fail "iFrame: cannot frame" φ
    |iFrameFinish].

Local Ltac iFrameAnyPure :=
  repeat match goal with H : _ |- _ => iFramePure H end.

Local Ltac iFrameAnyIntuitionistic :=
  iStartProof;
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => repeat iFrameHyp H; go Hs end in
  match goal with
  | |- envs_entails ?Δ _ =>
     let Hs := eval cbv in (env_dom (env_intuitionistic Δ)) in go Hs
  end.

Local Ltac iFrameAnySpatial :=
  iStartProof;
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => try iFrameHyp H; go Hs end in
  match goal with
  | |- envs_entails ?Δ _ =>
     let Hs := eval cbv in (env_dom (env_spatial Δ)) in go Hs
  end.

Tactic Notation "iFrame" := iFrameAnySpatial.

Tactic Notation "iFrame" "(" constr(t1) ")" :=
  iFramePure t1.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) ")" :=
  iFramePure t1; iFrame ( t2 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) ")" :=
  iFramePure t1; iFrame ( t2 t3 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) ")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 ).
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) constr(t8)")" :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 t8 ).

Local Ltac iFrame_go Hs :=
  lazymatch Hs with
  | [] => idtac
  | SelPure :: ?Hs => iFrameAnyPure; iFrame_go Hs
  | SelIntuitionistic :: ?Hs => iFrameAnyIntuitionistic; iFrame_go Hs
  | SelSpatial :: ?Hs => iFrameAnySpatial; iFrame_go Hs
  | SelIdent ?H :: ?Hs => iFrameHyp H; iFrame_go Hs
  end.

Tactic Notation "iFrame" constr(Hs) :=
  let Hs := sel_pat.parse Hs in iFrame_go Hs.
Tactic Notation "iFrame" "(" constr(t1) ")" constr(Hs) :=
  iFramePure t1; iFrame Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4) ")"
    constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) ")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 ) Hs.
Tactic Notation "iFrame" "(" constr(t1) constr(t2) constr(t3) constr(t4)
    constr(t5) constr(t6) constr(t7) constr(t8)")" constr(Hs) :=
  iFramePure t1; iFrame ( t2 t3 t4 t5 t6 t7 t8 ) Hs.


Lemma test2 (P Q: PROP) : P ∗ Q ⊢ P ∗ Q.
  iIntros "H".
  iDestruct (test with "H") as "?".
  iRename (IAnon (xO xH)) into "H".
  iDestruct "H" as "(HP&HQ)".
  iRename "HP" into "HQ".
  evar (i: ident).
  iAssert (named i P) with "[HP]" as "?".
  { unfold i. iFrame. }
  unfold i.
  iIntros "H". iDestruct "H" as "(?&?)". done.
Qed.
*)
End test.