From iris.proofmode Require Import tactics environments.

Set Default Proof Using "Type".

Implicit Types (name: string).

Definition named {A} (name: string) (P: A): A := P.
Infix "∷" := named (at level 79, no associativity).

Class IntoNamed {PROP: bi} (P: PROP) (name: string) (Q: PROP) :=
  into_named : P ⊢ Q.
Arguments IntoNamed {_} _%I _%string _%I : simpl never.
Hint Mode IntoNamed + ! - - : typeclass_instances.

(* IntoNamedSep is intended to destruct P into [Q ∗ R] and name the first
conjunct *)
Class IntoNamedSep {PROP: bi} (P: PROP) (name: string) (Q: PROP) (R: PROP) :=
  into_named_sep : P ⊢ Q ∗ R.
Arguments IntoNamedSep {_} _%I _%string _%I _%I : simpl never.
Hint Mode IntoNamedSep + ! - - - : typeclass_instances.

Class IntoNamedAnd {PROP: bi} (P: PROP) (name: string) (Q: PROP) (R: PROP) :=
  into_named_and : P ⊢ Q ∧ R.
Arguments IntoNamedAnd {_} _%I _%string _%I _%I : simpl never.
Hint Mode IntoNamedAnd + ! - - - : typeclass_instances.

Section bi.
  Context {PROP: bi}.
  Implicit Types (P:PROP).
  Global Instance named_IntoNamed P name :
    IntoNamed (name ∷ P) name P.
  Proof. rewrite /IntoNamed /named //. Qed.

  Global Instance into_named_sep_named P name Q :
    IntoNamedSep (name ∷ P ∗ Q) name P Q.
  Proof. rewrite /IntoNamedSep /named //. Qed.

  Global Instance into_named_and_named P name Q :
    IntoNamedAnd (named name P ∧ Q) name P Q.
  Proof. rewrite /IntoNamedAnd /named //. Qed.

  Inductive dummy {A} (x:A) : Prop := mkDummy.
  Hint Resolve mkDummy : core.
  Arguments mkDummy {_ _}.

  Ltac destruct_env :=
    match goal with
    | [ H: match ?d with | Some Δ => _ | None => False end |- _ ] =>
      destruct d as [Δ|] eqn:Hrep; [ | contradiction H ]
    end.

  Lemma tac_destruct_name_one Δ i p P Q R Q' name :
    envs_lookup i Δ = Some (p, P) →
    (if p then IntoNamedAnd P name Q R else IntoNamedSep P name Q R) →
    match envs_simple_replace i p (Esnoc (Esnoc Enil i R) (INamed name) Q) Δ with
    | Some Δ' => dummy name → envs_entails Δ' Q'
    | None => False
    end →
    envs_entails Δ Q'.
  Proof.
    rewrite envs_entails_eq => ?? HQ.
    destruct_env.
    rewrite envs_simple_replace_sound //.
    simpl.
    rewrite (HQ mkDummy).
    destruct p; simpl.
    - rewrite (into_named_and (P:=P)).
      rewrite right_id.
      apply bi.wand_elim_r.
    - rewrite (into_named_sep (P:=P)).
      rewrite right_id.
      apply bi.wand_elim_r.
  Qed.
End bi.
