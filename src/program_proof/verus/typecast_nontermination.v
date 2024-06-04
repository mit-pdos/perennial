Require Import Coq.Classes.DecidableClass.
From stdpp Require Import base.

Program Definition cast (A:Prop) (B:Prop) (Heq:A = B) (e:A) : B.
Proof.
  rewrite <- Heq.
  refine e.
Defined.

(* Axiom lem : (∀ P:Prop, (P ∨ ¬P)). *)
Instance lem_all P : Decision P.
Admitted.

Definition cast2 (A:Prop) (B:Prop) (e1:A) (e2:B) : B.
Proof.
  destruct (decide (A = B)).
  { rewrite <- e. refine e1. }
  refine e2.
Defined.

Definition D : Prop := ∀ {A:Prop}, A → A.
Definition callD (e:D) : (D → D) := e D.
Definition makeD (e:D → D) : D :=
   λ a, cast2 (D → D) (a → a) e (λ (x:a), x).

Definition ω : D := makeD (λ (x:D), (callD x) x).
Definition Ω : D := (callD ω) ω.

Lemma y : ω = (callD ω) ω.
Proof.
  pose ω.
  unfold ω in *.
  unfold callD.
  unfold makeD at 2.
  destruct (decide ((D → D) = (D → D))).
  2:{ exfalso. apply n. reflexivity. }
  unfold eq_ind.
  cbv.
  simpl.

Lemma x : Ω = Ω Ω.
Proof.
  pose Ω.
  unfold Ω in *.
  Eval simpl in d.
  Eval simpl in Ω.

(* μ t, t → t *)

Inductive unitype : Prop :=
  cons : (∀ α, (α → unitype)) → unitype.

(*
Inductive onetype : Prop :=
  | cons : (onetype → onetype) → onetype. *)

Definition unfld2 (x:unitype) : (unitype → unitype).
Proof.
  intros.
  refine x.
Defined.

(*
Definition ω2 : unitype :=
  cons (
      λ α,
      λ (x:α),
        (* XXX: want type casting here. *)
        match x with
        | cons f => f _ x
        end
    )
. *)

Definition Y : (D → D) → D :=
  λ f, (λ (x:D), f ((callD x) x)) (λ (x:D), f ((callD x) x)).


Lemma prove_bad : False.
Proof.
  apply proof (Y False _).
  eauto.
  Unshelve. eauto.
Qed.

Definition Ω2 :=
  x x
.
