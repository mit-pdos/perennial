(* Just reexport Iris mdoule *)
From iris.base_logic Require Export lib.ghost_var.

(* Add some Perennial-specific stuff *)
From Perennial.algebra Require Import own_discrete atleast.

Set Default Proof Using "Type".

Section lemmas.
  Context `{!ghost_varG Σ A}.
  Implicit Types (a : A) (q : Qp).

  Global Instance ghost_var_discrete γ q a : Discretizable (ghost_var γ q a).
  Proof. rewrite ghost_var_eq. apply _. Qed.

  Global Instance ghost_var_abs_timeless γ q a : AbsolutelyTimeless (ghost_var γ q a).
  Proof. rewrite ghost_var_eq. apply _. Qed.

End lemmas.


From iris.proofmode Require Import coq_tactics intro_patterns spec_patterns.
From iris.proofmode Require Import tactics.
From stdpp Require Import hlist pretty.

(* This tactic searches for own H (● (Excl' x)) and own H (◯ (Excl' y)) in the context and
   uses ghost_var_agree to prove that x = y. *)
Tactic Notation "unify_ghost_var" constr(γ) :=
  match goal with
  | [ |- context[ environments.Esnoc _ (INamed ?auth_name) (ghost_var γ _ ?x)] ] =>
    match goal with
    | [ |- context[ environments.Esnoc _ (INamed ?frag_name) (ghost_var γ _ ?z)] ] =>
      (* make sure these are two different names *)
      let eq := constr:(bool_decide (auth_name = frag_name)) in
      match (eval hnf in eq) with
      | true => fail 1 (* backtrack to next match *)
      | false =>
        let pat := constr:([(SIdent (INamed auth_name) nil); (SIdent (INamed frag_name) nil)]) in
        (* TODO: can we write this with a fresh variable rather than Hp, and using
        inversion Hp; subst; clear Hp (which is less buggy than
        inversion_clear)? *)
        (iDestruct (ghost_var_agree with pat) as %Hp; inversion_clear Hp; subst; [])
      end
    end
  end.
