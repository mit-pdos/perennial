From stdpp Require Import base option fin_maps.
From Perennial.Helpers Require Import Integers.

Ltac solve_inhabited :=
  lazymatch goal with
  | [ |- Inhabited _ ] => apply populate; constructor; apply inhabitant
  end.

Notation "'populate!'" := (ltac:(solve_inhabited)) (at level 0, only parsing).

Tactic Notation "fmap_Some" "in" hyp(H) "as" simple_intropattern(x) :=
  try lazymatch type of H with
      | @lookup _ _ (list _) _ _ (fmap _ _) = _ =>
        rewrite list_lookup_fmap in H
      | lookup _ (fmap _ _) = _ =>
        rewrite lookup_fmap in H
      end ;
  lazymatch type of H with
  | fmap _ _ = Some ?v =>
    let Heq := fresh "Heq" in
    apply fmap_Some_1 in H as [x [H Heq]];
    try (is_var v; subst v)
  | _ => fail 1 "fmap_Some:" H "is not an fmap equality"
  end.

Tactic Notation "fmap_Some" "in" hyp(H) := fmap_Some in H as ?.

Ltac exact_eq H :=
  match type of H with
  | ?x =>
    match goal with
    | |- ?y =>
      assert (x = y) as <-; [f_equal|assumption]
    end
  end.

(* No built-in replace (see https://github.com/rocq-prover/rocq/issues/15009).
   This introduces a tactic notation so that the open_constrs can introduce new
   evars before being passed into the builtin [replace] tactic.
 *)
Tactic Notation "ereplace" open_constr(x) "with" open_constr(y) :=
  replace x with y.

Tactic Notation "ereplace" open_constr(x) "with" open_constr(y) "by" tactic(s) :=
  replace x with y by s.

(* TODO: [constr] doesn't support [occurrence] clauses like [in *]. *)
Tactic Notation "ereplace" open_constr(x) "with" open_constr(y) "in" constr(z) :=
  replace x with y in z.

Tactic Notation "ereplace" open_constr(x) "with" open_constr(y) "in" constr(z) "by" tactic(s) :=
  replace x with y in z by s.
