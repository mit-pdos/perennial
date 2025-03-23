From Coq Require Import ZArith.
From Coq Require Import ssreflect.
From stdpp Require Import base numbers.
From Perennial.Helpers Require Import Integers.

Open Scope Z_scope.
Set Default Goal Selector "!".
Set Default Proof Using "Type".

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Theorem sum_overflow_check (x y: u64) :
  uint.Z (word.add x y) < uint.Z x <-> uint.Z x + uint.Z y >= 2^64.
Proof. word. Qed.

Lemma sum_nooverflow_l (x y : u64) :
  uint.Z x ≤ uint.Z (word.add x y) →
  uint.Z (word.add x y) = (uint.Z x) + (uint.Z y).
Proof. word. Qed.

Lemma word_add_comm (x y : u64) :
  word.add x y = word.add y x.
Proof. word. Qed.

Lemma sum_nooverflow_r (x y : u64) :
  uint.Z y ≤ uint.Z (word.add x y) →
  uint.Z (word.add x y) = (uint.Z x) + (uint.Z y).
Proof. word. Qed.

Theorem word_add1_neq (x: u64) :
  uint.Z x ≠ uint.Z (word.add x (W64 1)).
Proof. word. Qed.

(* avoid leaving it at div_mod_to_equations since it causes some backwards
incompatibility *)
Ltac Zify.zify_post_hook ::= idtac.
