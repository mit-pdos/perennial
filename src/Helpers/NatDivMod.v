(* import ZifyNat to bring some Zify instances into scope *)
Require Import ZArith ZifyInst ZifyNat Lia.

(* the user should probably also use this - we don't (yet) enable it globally in
Perennial *)
#[local] Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Goal forall (n:nat), 2 * n mod 2 = 0.
Proof.
  intros.
  lia.
Qed.
