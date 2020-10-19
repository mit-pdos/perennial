From stdpp Require Import base option fin_maps.

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
