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

Global Instance named_persistent {PROP: bi} i (P: PROP) : Persistent P → Persistent (named i P).
Proof. rewrite named_eq /named_def//=. Qed.

Global Instance named_affine {PROP: sbi} i (P: PROP) : Affine P → Affine (named i P).
Proof. rewrite named_eq /named_def//=. Qed.

Global Instance named_timeless {PROP: sbi} i (P: PROP) : Timeless P → Timeless (named i P).
Proof. rewrite named_eq /named_def//=. Qed.

Global Instance named_absorbing {PROP: bi} i (P: PROP) : Absorbing P → Absorbing (named i P).
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

Class IntoAndEnv {PROP : bi} (p: bool) (P: PROP) (Ps: prop_list PROP) :=
  into_and_env : □?p P ⊢ □?p [∧] (pl2p Ps).
Arguments IntoAndEnv {_} _ _%I _%I : simpl never.
Arguments into_and_env {_} _ _%I _%I {_}.
Hint Mode IntoAndEnv + + ! - : typeclass_instances.

Class FrameSepEnv {PROP : bi} (Δ Δ' : envs PROP) (P Q : PROP) :=
  frame_env : ∃ R, (of_envs Δ ⊢ (R ∗ of_envs Δ')) ∧ (R -∗ Q -∗ P).
Arguments FrameSepEnv {_} _%I _%I _%I _%I.
Arguments frame_env {_} _%I _%I _%I _%I {_}.
Hint Mode FrameSepEnv + + - + - : typeclass_instances.

(* Above we pass in the context and cancel as we go, but then the context
   re-appears repeatedly, and you can't abstract it because of an evar. Maybe we
   should instead generate a term with holes in it, along with a list of
   names/props, and then check each name to see if it is in the context or not
   with the appropriate form, and then fill in the holes based on whether we
   could cancel?  *)

(*
Class FrameSepEnv {PROP : bi} (Rs : prop_list PROP) (P Q : PROP) := frame_env : [∗] (pl2p Rs) ∗ Q ⊢ P.
Arguments FrameSepEnv {_} _%I _%I _%I.
Arguments frame_env {_} _%I _%I _%I {_}.
Hint Mode FrameSepEnv + - ! + : typeclass_instances.
*)

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

Global Instance positive_into_and_sep:
  BiPositive PROP → ∀ (P : PROP) (Ps : prop_list PROP), IntoSepEnv P Ps → IntoAndEnv true P Ps.
Proof.
  intros HPOS P Ps.
  rewrite /IntoSepEnv/IntoAndEnv => ->. simpl.
  induction Ps => //=; auto.
  rewrite intuitionistically_sep intuitionistically_and.
  iIntros "(?&?)". iFrame. by iApply IHPs.
Qed.

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

Implicit Types P Q R : PROP.

Global Instance frame_env_here_absorbing Δ Δ' i (R: PROP) :
  Absorbing R →
  envs_lookup_delete false i Δ = Some (false, R, Δ') →
  FrameSepEnv Δ Δ' (named i R) True | 0.
Proof.
  rewrite /FrameSepEnv => ? Hsound.
  exists R; split.
  * rewrite envs_lookup_delete_sound //=; simpl; auto.
  * iIntros "??". rewrite named_eq. iFrame.
Qed.
Global Instance frame_env_here Δ Δ' i (R: PROP) :
  envs_lookup_delete false i Δ = Some (false, R, Δ') →
  FrameSepEnv Δ Δ' (named i R) emp | 1.
Proof.
  rewrite /FrameSepEnv => Hsound.
  exists R; split.
  * rewrite envs_lookup_delete_sound //=; simpl; auto.
  * iIntros "??". rewrite named_eq. iFrame.
Qed.

Global Instance frame_env_sep Δ Δ' Δ'' P1 P2 Q1 Q2 :
  FrameSepEnv Δ Δ' P1 Q1 →
  FrameSepEnv Δ' Δ'' P2 Q2 →
  FrameSepEnv Δ Δ'' (P1 ∗ P2) (Q1 ∗ Q2).
Proof.
  rewrite /FrameSepEnv.
  intros (R1&HR1&HR1').
  intros (R2&HR2&HR2').
  exists (R1 ∗ R2)%I.
  split.
  - rewrite HR1 HR2. by rewrite assoc.
  - rewrite HR1' HR2'. iIntros "(Hw1&Hw2) (H1&H2)".
    iSplitL "Hw1 H1".
    * by iApply "Hw1".
    * by iApply "Hw2".
Qed.

Global Instance frame_env_sep_miss Δ P:
  FrameSepEnv Δ Δ P P | 100.
Proof.
  rewrite /FrameSepEnv. exists emp%I. split; eauto.
Qed.

Lemma tac_frame_env Δ Δ' P Q :
  FrameSepEnv Δ Δ' P Q →
  envs_entails Δ' Q →
  envs_entails Δ P.
Proof.
  rewrite /FrameSepEnv.
  intros (R&HR&HR').
  rewrite envs_entails_eq HR HR' => ->.
  apply wand_elim_l.
Qed.

(*
Global Instance frame_env_sep Δ Δ' P1 Q1 Q2 :
  FrameSepEnv Δ Δ' P1 Q1 →
  FrameSepEnv Δ Δ' (P1 ∗ Q2) (Q1 ∗ Q2).
Proof.
  rewrite /FrameSepEnv => H.
  destruct H as (R&H1&H2).
  exists R. split; auto.
  rewrite H2. iIntros "Hwand (?&?)".
  iFrame. by iApply "Hwand".
Qed.
*)

(*
Global Instance frame_env_here_absorbing Δ Δ' i (R: PROP) :
  Absorbing R →
  envs_lookup_delete false i Δ = Some (false, R, Δ') →
  FrameSepEnv Δ Δ' (named i R) True | 0.
Proof.
  intros. rewrite /FrameSepEnv.
  rewrite envs_lookup_delete_sound //=; simpl.
  rewrite -assoc sep_elim_l named_eq //=.
Qed.
Global Instance frame_env_here Δ Δ' i (R: PROP) :
  envs_lookup_delete false i Δ = Some (false, R, Δ') →
  FrameSepEnv Δ Δ' (named i R) emp | 1.
Proof.
  intros. rewrite /FrameSepEnv.
  rewrite envs_lookup_delete_sound //=; simpl.
  rewrite -assoc wand_elim_r right_id named_eq //=.
Qed.

Global Instance frame_env_sep Δ Δ' P1 Q1 Q2 :
  FrameSepEnv Δ Δ' P1 Q1 →
  FrameSepEnv Δ Δ' (P1 ∗ Q2) (Q1 ∗ Q2).
Proof.
  rewrite /FrameSepEnv. iIntros (H1) "H".
  iDestruct "H" as "(HΔ&Hwand)".
  assert (
  iPoseProof (H1 with "[-]") as "HP1".
  iFrame. iIntros "HΔ'".

*)

(*
Global Instance frame_env_sep Δ Δ' Δ'' P1 P2 Q1 Q2 :
  FrameSepEnv Δ Δ' P1 Q1 →
  FrameSepEnv Δ' Δ'' P2 Q2 →
  FrameSepEnv Δ Δ'' (P1 ∗ P2) (Q1 ∗ Q2).
Proof.
  rewrite /FrameSepEnv. iIntros (H1 H2) "H".
  iDestruct "H" as "(HΔ&Hwand)".
  iPoseProof (H1 with "[-]") as "HP1".
  iFrame. iIntros "HΔ'".
*)

(*
Global Instance frame_env_here_absorbing i (R: PROP) :
  Absorbing R → FrameSepEnv [(LNamed i, R)] (named i R) True | 0.
Proof. intros. by rewrite /FrameSepEnv//= sep_elim_l right_id. Qed.
Global Instance frame_env_here i R : FrameSepEnv [(LNamed i, R)] (named i R) emp | 1.
Proof. intros. by rewrite /FrameSepEnv//= sep_elim_l right_id. Qed.
Global Instance frame_env_sep Rs1 Rs2 P1 P2 Q1 Q2 :
  FrameSepEnv Rs1 P1 Q1 →
  FrameSepEnv Rs2 P2 Q2 →
  FrameSepEnv (Rs1 ++ Rs2) (P1 ∗ P2) (Q1 ∗ Q2).
Proof. rewrite /FrameSepEnv//=. /MakeSep => <- <-. by rewrite assoc. Qed.
Global Instance frame_env_miss R : FrameSepEnv [] R R | 100.
Proof. intros. by rewrite /FrameSepEnv//= left_id. Qed.
*)

Lemma tac_sep_list_destruct Δ Δ' i p Γ bump (P: PROP) (Ps: prop_list PROP) Q :
  envs_lookup i Δ = Some (p, P) →
  (if p then IntoAndEnv true P Ps else IntoSepEnv P Ps) →
  pl_env_expand (env_counter Δ) Ps Enil = (bump, Γ) →
  envs_simple_replace i p Γ Δ = Some Δ' →
  envs_entails (envs_set_counter Δ' bump) Q → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => Hlookup Hsep Hexpand Hrepl Himpl.
  rewrite envs_simple_replace_sound //=.
  assert (Hrec1: ∀ p (Γ: env PROP), ([∗] Γ -∗ [∗] pl2p Ps -∗ [∗] snd (pl_env_expand p Ps Γ))%I).
  { clear. induction Ps => //= p Γ.
    * iIntros "H"; eauto.
    * iIntros "H1 (a&H2)".
      destruct a as ([]&?); simpl;
      iApply (IHPs with "[a H1] H2"); iFrame.
  }
  assert (Hrec2: ∀ p (Γ: env PROP), (□ [∧] Γ -∗ □ [∧] pl2p Ps -∗ □ [∧] snd (pl_env_expand p Ps Γ))%I).
  { clear. induction Ps => //= p Γ.
    * iIntros "H"; eauto.
    * iIntros "#H1 #(a&H2)".
      destruct a as ([]&?); simpl;
      iApply (IHPs with "[a H1] H2"); iFrame;
      simpl;
      iApply intuitionistically_and;
      iSplit; simpl; iFrame "#".
  }
  specialize (Hrec1 (env_counter Δ) Enil). rewrite Hexpand in Hrec1.
  specialize (Hrec2 (env_counter Δ) Enil). rewrite Hexpand in Hrec2.
  destruct p.
  - rewrite (into_and_env true P). simpl.
    iIntros "(Hps&Hwand)".
    iPoseProof (Hrec2 with "[ ] [$]") as "HPs'".
    simpl; iAlways; trivial. simpl.
    rewrite envs_set_counter_sound in Himpl * => ->.
    by iApply "Hwand".
  - rewrite (into_sep_env P). simpl.
    iIntros "(Hps&Hwand)".  iPoseProof (Hrec1 with "[$] [$]") as "HPs'".
    rewrite envs_set_counter_sound in Himpl * => ->.
    by iApply "Hwand".
Qed.
End list_destruct.

Ltac set_counter_reduce :=
  match goal with |- ?u => let v := eval cbv [envs_set_counter] in u in change v end.

Ltac iLDestructEx H :=
  match goal with
  | [ |- context[ environments.Esnoc _ (INamed H) (bi_exist (fun x => _))%I ]] =>
    iDestruct H as (x) H
  | [ |- context[ environments.Esnoc _ H (bi_exist (fun x => _))%I ]] =>
    iDestruct H as (x) H
  end.

Ltac iLDestructCore H :=
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

Ltac iLDestruct H := repeat (try iLDestructEx H); iLDestructCore H.

Ltac iLIntro :=
  let H := iFresh in iIntros H; iLDestruct H.

Ltac iLIntroP :=
  let H := iFresh in
  let pat :=constr:(IAlwaysElim (IIdent H)) in
  iIntros H; iLDestruct H.

Section test.
Context {PROP: bi}.
Context {Hpos: BiPositive PROP}.
Context {P P' : nat → PROP}.

Context (HPP': ∀ n, P n ⊢ P' n).

Definition test_list := pl2p [ (LNamed "Hfoo", P O); (LAnon, P' O)  ].
Fixpoint bigterm_list (P: nat → PROP) s n :=
  match n with
  | O => []
  | S n' => (LNamed s, P (S n')) :: bigterm_list P (String "a" s) n'
  end.

Lemma Hex_destruct : (∃ foo : nat, (named "bar" True)) ⊢ (True : PROP).
Proof.
  iIntros "H". iLDestruct "H".
  auto.
Qed.

Lemma Hpers_ldestruct : (∃ foo : nat, named "bar" (□ emp) ∗ named "foo" (□ emp)%I) ⊢ (True : PROP).
Proof using Hpos.
  iIntros "#H". iLDestruct "H".
  auto.
Qed.

Lemma Hpers_intro_ldestruct :
  (∃ foo : nat, named "bar" (□ emp) ∗ named "foo" (□ emp)%I) ⊢ (True : PROP).
Proof using Hpos.
  iLIntroP. auto.
Qed.

Lemma HPP_destruct_named : True ∗ [∗] test_list ∗ True ⊢ P O -∗ P O -∗ P O -∗ P O -∗ [∗] test_list.
Proof.
  iIntros "(?&H0&H1)".
  iLDestruct "H0".
Abort.

Lemma HPP_intro_named : [∗] test_list ⊢ P O -∗ P O -∗ P O -∗ P O -∗ [∗] test_list.
Proof.
  iLIntro.
Abort.

Lemma Hbig : [∗] (pl2p (bigterm_list P "a" 20)) ⊢ True.
Proof.
  iLIntro.
  auto.
Qed.


(*
Lemma Hbig_slow : [∗] (pl2p (bigterm_list P "a" 20)) ⊢ True.
Proof.
  simpl.
  iDestructIntro.
  auto.
Time Qed.
*)

Lemma Hbig_combined : [∗] (pl2p (bigterm_list P "a" 20)) -∗ [∗] (pl2p (bigterm_list P "b" 20)) -∗ True.
Proof.
  iLIntro.
  iLIntro.
  auto.
Qed.
Hint Extern 10 (envs_lookup_delete _ _ _ = Some _) => (compute; reflexivity) : typeclass_instances.

(*
Lemma Hbig_frame : [∗] (pl2p (bigterm_list P "a" 20)) ⊢ [∗] (pl2p (bigterm_list P "a" 20)).
Proof.
  simpl. iLIntro.
  (*
  iNamed (iFrame).
  Time Qed.
   *)
  (*
  evar (Δ : envs PROP).
  match goal with
  | [ |- envs_entails ?Γ _ ] => assert ((envs_lookup_delete false "a" Γ = Some (false, P 20, Δ)))
  end.
   *)
  Print Esnoc.
  match goal with
  | [ |- context [(Esnoc _ (IAnon ?x) _)]] => idtac x
  end.
  eapply tac_frame_env.
  apply _.
  abstract(
  assert (
      emp -∗
  (emp : PROP)
  ∗ emp
    ∗ emp
      ∗ emp
        ∗ emp
          ∗ emp
          ∗ emp ∗ emp ∗ emp ∗ emp ∗ emp ∗ emp ∗ emp ∗ emp ∗ emp ∗ emp ∗ emp ∗ emp ∗ emp ∗ emp ∗ emp);
  abstract (rewrite ?left_id //=);
  by iApply H).
Time Qed.
*)

(*
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
*)
End test.

Hint Extern 10 (envs_lookup_delete _ _ _ = Some _) => (compute; reflexivity) : typeclass_instances.
