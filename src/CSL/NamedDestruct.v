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
Definition named_eq {PROP : bi} : @named PROP = @named_def PROP := (@named_aux PROP).(seal_eq).

Global Instance named_timeless {PROP: sbi} i (P: PROP) : Timeless P → Timeless (named i P).
Proof. rewrite named_eq /named_def//=. Qed.

Global Instance named_frame_here :
  ∀ (PROP : bi) i (p : bool) (R : PROP), Frame p (named i R) R emp | 100.
Proof. intros ???. rewrite named_eq /named_def //=//=. apply _. Qed.

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
  induction Γs; rewrite //= named_eq /named_def IHΓs //=.
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
  rewrite ?named_eq;
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

Inductive LTag : Set :=
| LNamed : string → LTag
| LAnon : LTag.
Coercion LNamed : string >-> LTag.

Definition tagged_prop (PROP: bi) := (LTag * PROP)%type.
Definition tagged_to_prop {PROP} (tP: tagged_prop PROP) : PROP :=
  match tP with
  | (LNamed s, P) => named s P
  | (LAnon, P) => P
  end.
Definition prop_list (PROP: bi) := list (tagged_prop PROP).
Definition pl2p {PROP : bi} (Ps: prop_list PROP) : list PROP := map (tagged_to_prop) Ps.
Definition pl2pp {PROP : bi} (Ps: prop_list PROP) := ([∗] (pl2p Ps))%I.


Class IntoSepEnv {PROP : bi} (P: PROP) (Ps: prop_list PROP) :=
  into_sep_env : P ⊢ [∗] (pl2p Ps).
Arguments IntoSepEnv {_} _%I _%I : simpl never.
Arguments into_sep_env {_} _%I _%I {_}.
Hint Mode IntoSepEnv + ! - : typeclass_instances.

Definition envs_set_counter {PROP} (Δ : envs PROP) (p: positive) : envs PROP :=
  Envs (env_intuitionistic Δ) (env_spatial Δ) p.
Lemma envs_set_counter_equiv {PROP} (Δ : envs PROP) p : envs_Forall2 (⊣⊢) Δ (envs_set_counter Δ p).
Proof. done. Qed.
Lemma envs_set_counter_sound {PROP} (Δ: envs PROP) p : of_envs (envs_set_counter Δ p) ⊣⊢ of_envs Δ.
Proof. by f_equiv. Qed.

Section list_destruct.
Context {PROP: bi}.
Fixpoint pl_env_expand (p: positive) (Ps: prop_list PROP) (Γ: env PROP) : positive * env PROP :=
  match Ps with
  | nil => (p, Γ)
  | (LAnon, P) :: Ps' => pl_env_expand (Pos_succ p) Ps' (Esnoc Γ (IAnon p) P)
  | (LNamed s, P) :: Ps' => pl_env_expand p Ps' (Esnoc Γ s P)
  end.
Global Instance env_into_sep_env (Ps: prop_list PROP) : IntoSepEnv ([∗] pl2p Ps) Ps.
Proof. rewrite /IntoSepEnv. trivial. Qed.

Global Instance sep_into_sep_single_named (i: string) (P: PROP) :
  IntoSepEnv (named i P) [(LNamed i, P)].
Proof. rewrite /IntoSepEnv//=. iFrame. eauto. Qed.

Global Instance sep_into_sep_cons (i: string) (P Q: PROP) Ps :
  IntoSepEnv Q Ps →
  IntoSepEnv (named i P ∗ Q) ((LNamed i, P) :: Ps).
Proof. rewrite /IntoSepEnv//=. iIntros (H1) "(?&?)". iFrame. by iApply H1. Qed.

Global Instance sep_into_sep_single_anon (P: PROP) :
  IntoSepEnv P [(LAnon, P)] | 100.
Proof. rewrite /IntoSepEnv//=. iFrame. eauto. Qed.

Lemma tac_sep_list_destruct Δ Δ' i Γ bump (P: PROP) (Ps: prop_list PROP) Q :
  envs_lookup i Δ = Some (false, P) →
  IntoSepEnv P Ps →
  pl_env_expand (env_counter Δ) Ps Enil = (bump, Γ) →
  envs_simple_replace i false Γ Δ = Some Δ' →
  envs_entails (envs_set_counter Δ' bump) Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => Hlookup Hsep Hexpand Hrepl Himpl.
  rewrite envs_simple_replace_sound //=.
  rewrite /= (into_sep_env P).
  assert (Hrec: ∀ p (Γ: env PROP), ([∗] Γ -∗ [∗] pl2p Ps -∗ [∗] snd (pl_env_expand p Ps Γ))%I).
  { clear. induction Ps => //= p Γ.
    * iIntros "H"; eauto.
    * iIntros "H1 (a&H2)".
      destruct a as ([]&?); simpl;
      iApply (IHPs with "[a H1] H2"); iFrame.
  }
  specialize (Hrec (env_counter Δ) Enil). rewrite Hexpand in Hrec.
  iIntros "(HPs&HIH)". iPoseProof (Hrec with "[$] [$]") as "HPs'".
  rewrite envs_set_counter_sound in Himpl * => ->.
  by iApply "HIH".
Qed.
End list_destruct.

Ltac set_counter_reduce :=
  match goal with |- ?u => let v := eval cbv [envs_set_counter] in u in change v end.

Ltac iLDestruct H :=
  eapply (tac_sep_list_destruct _ _ H);
  [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iLDestruct:" H "not found"
  |apply _
  |pm_reflexivity ||
     fail "iLDestruct: some name not fresh"
  |pm_reflexivity ||
     fail "iLDestruct: some name not fresh"
  |set_counter_reduce; pm_reduce].

Ltac iLIntro :=
  let H := iFresh in iIntros H; iLDestruct H.

Section test.
Context {PROP: bi}.
Context {P P' : PROP}.

Context (HPP': P ⊢ P').

Definition test_list := pl2p [ (LNamed "Hfoo", P); (LAnon, P')  ].
Fixpoint bigterm_list (P: PROP) n :=
  match n with
  | O => []
  | S n' => (LAnon, P) :: bigterm_list P n'
  end.

Lemma HPP_destruct_named : True ∗ [∗] test_list ∗ True ⊢ P -∗ P -∗ P -∗ P -∗ [∗] test_list.
Proof.
  iIntros "(?&H0&H1)".
  iLDestruct "H0".
Abort.

Lemma HPP_intro_named : [∗] test_list ⊢ P -∗ P -∗ P -∗ P -∗ [∗] test_list.
Proof.
  iLIntro.
Abort.

Lemma Hbig : [∗] (pl2p (bigterm_list P 20)) ⊢ True.
Proof.
  iLIntro.
  auto.
Qed.

(*
Lemma Hbig_slow : [∗] (pl2p (bigterm_list P 20)) ⊢ True.
Proof.
  simpl.
  iDestructIntro.
  auto.
Qed.
*)

Lemma Hbig_combined : [∗] (pl2p (bigterm_list P 20)) -∗ [∗] (pl2p (bigterm_list P 20)) -∗ True.
  iLIntro.
  iLIntro.
  auto.
Qed.

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