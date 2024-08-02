From New.proof Require Import grove_prelude.

Section definitions.

Context `{!heapGS Σ}.

Context {typ : Type}.
Context {typ_eqb : typ → typ → bool}.

Inductive prop :=
| prop_own : nat → prop
| prop_sep : prop → prop → prop
| prop_wand : prop → prop → prop
| prop_var : string → prop
| prop_forall (x : string) (A : typ) : prop → prop
.

Fixpoint prop_eqb (P : prop) (Q : prop) : bool :=
  match P, Q with
  | prop_own n, prop_own m => Nat.eqb n m
  | prop_sep P Q, prop_sep P' Q' => prop_eqb P P' && prop_eqb Q Q'
  | prop_wand P Q, prop_wand P' Q' => prop_eqb P P' && prop_eqb Q Q'
  | prop_var x, prop_var y => String.eqb x y

  (* XXX: no α-conversion *)
  | prop_forall x A P, prop_forall x' A' P'  => String.eqb x x' && typ_eqb A A' && prop_eqb P P'
  | _, _ => false
  end.

Declare Scope prop_scope.
Delimit Scope prop_scope with prop_scope.
Notation "P ∗ Q" := (prop_sep P%prop_scope Q%prop_scope) : prop_scope.
Notation "P -∗ Q" := (prop_wand P%prop_scope Q%prop_scope) : prop_scope.

Bind Scope prop_scope with prop.

Inductive term :=
| cons_sep (el : term) (er : term) : term
| lam (x : string) (e : term) : term
| var (x : string)
.

Definition typing_context : Type := list (string * prop).

Definition context_lookup := (assocl_lookup (A:=prop)).

Fixpoint context_delete (s : string) (Γ : typing_context) : typing_context :=
  match Γ with
  | [] => []
  | (n,P) :: Γ => if (String.eqb n s) then (context_delete s Γ) else (n,P) :: (context_delete s Γ)
  end
.

Fixpoint has_type_internal (Γ : typing_context) (t : term) (P : prop) : (bool * typing_context) :=
  match P, t with
  | prop_sep P Q, cons_sep el er =>
      let '(bl, Γ) := has_type_internal Γ el P in
      let '(br, Γ) := has_type_internal Γ er Q in
      (bl && br, Γ)
  | prop_wand P Q, lam x e =>
      has_type_internal ((x,P)::Γ) e Q
  | _, var x => match (context_lookup x Γ) with
               | Some P' => (prop_eqb P' P, context_delete x Γ)
               | _ => (false, [])
               end
  | _, _ => (false, [])
  end.

Definition type_check (t : term) (P : prop) : bool := fst (has_type_internal [] t P).

Definition proof : term :=
  lam "HP" (lam "HQ" $ cons_sep (var "HP") (var "HQ")).

Definition P := prop_own 10.
Definition Q := prop_own 11.

Eval compute in type_check proof (P -∗ Q -∗ (P ∗ Q)).

Goal ∀ (P' Q': iProp Σ), P' -∗ Q' -∗ P' ∗ Q'.
Proof.
  iIntros (??) "$ $".
  Show Proof.
  Print proof.
Qed.

Lemma r S : prop_eqb S S = true.
Proof.
  induction S.
  - simpl. by rewrite Nat.eqb_refl.
  - simpl. rewrite IHS1 IHS2. done.
  - simpl. rewrite IHS1 IHS2. done.
  - simpl.
Abort.

Lemma general S T :
  type_check proof (S -∗ T -∗ (S ∗ T)).
Proof.
  unfold type_check.
  simpl.
  Show Proof.
Abort.

Lemma tac_wand_intro (i : ident) (Δ : envs (iProp Σ)) (P Q : iProp Σ) :
  match envs_app false (Esnoc Enil i P) Δ with
  | Some Δ' => envs_entails Δ' Q
  | None => False
  end → envs_entails Δ (P -∗ Q)
.
Proof.
Admitted.

Fixpoint nwand n P : iProp Σ :=
  match n with
  | O => True
  | S n => P -∗ (nwand n P)
  end
.

Fixpoint nimpl n P : Prop :=
  match n with
  | O => True
  | S n => P -> (nimpl n P)
  end
.

Lemma test_impl P :
  nimpl 1000 P
.
Proof.
  repeat intros ?.
  refine I.
Time Qed.
(* Finished transaction in 1.161 secs (1.16u,0.s) (successful) *)

Lemma test P :
  ⊢ nwand 100 P
.
Proof.
  iStartProof.
  repeat iIntros "?".
  done.
Time Qed.
(*
50: 0.042
100: 0.167
200: 0.682
300: 1.765
400: 3.192
500: 4.973
1000: 20.68
 *)

End definitions.
