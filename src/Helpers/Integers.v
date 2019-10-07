From Coq Require Export BinNat.

From stdpp Require Import decidable countable.
From bbv Require Import Word.

Open Scope N_scope.

(* this is sort of a big number *)
Definition n64: nat := 64.
Notation u64 := (word n64).
Definition u64_max : N := Npow2 n64.
Opaque u64_max.

Instance word_eq_dec sz : EqDecision (word sz) := @weq sz.
Instance word_countable sz : Countable (word sz).
Proof.
  apply (inj_countable
           (@wordToN sz)
           (fun n => Some (NToWord sz n))); intros.
  by rewrite NToWord_wordToN.
Qed.

Instance wlt_decide sz : Decision (@wlt sz x y) := @wlt_dec sz.

(* TODO: note that these wrappers are inconvenient so we're actually using word
functions directly; if the indirection is useful we can add it and make u64
opaque *)

Definition add_u64 : u64 -> u64 -> u64 := @wplus _.
Definition minus_u64 : u64 -> u64 -> u64 := @wminus _.
Definition mult_u64 : u64 -> u64 -> u64 := @wmult _.

Definition u64_v : u64 -> N := @wordToN _.

Theorem u64_bound : forall (x:u64), u64_v x < u64_max.
Proof.
  intros.
  apply wordToN_bound.
Qed.

Definition byte := (word 8).
