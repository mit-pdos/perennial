Require Import Arith ZArith ZifyClasses ZifyInst Lia.

(* adapted from https://github.com/coq/coq/issues/11447#issuecomment-714308921 *)

#[local] Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Goal forall (n:nat), 2 * n mod 2 = 0.
Proof.
  intros.
  Fail lia.
Abort.

Program Instance Op_Nat_mod : BinOp Nat.modulo :=
  {| TBOp := Z.modulo ; TBOpInj := Nat2Z.inj_mod |}.
Add Zify BinOp Op_Nat_mod.
Program Instance Op_Nat_div : BinOp Nat.div :=
  {| TBOp := Z.div ; TBOpInj := Nat2Z.inj_div |}.
Add Zify BinOp Op_Nat_div.

Goal forall (n:nat), 2 * n mod 2 = 0.
Proof.
  intros.
  lia.
Qed.
