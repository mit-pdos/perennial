From Coq Require Import List.
From stdpp Require Import list vector.
From Perennial.Helpers Require Import List Integers.

Lemma singleton_length {A} (x:A) : length [x] = 1%nat.
Proof. reflexivity. Qed.

Lemma length_cons {A} (x:A) xs : length (x::xs) = S (length xs).
Proof. reflexivity. Qed.

Lemma length_nil {A} : length (@nil A) = 0%nat.
Proof. reflexivity. Qed.

Create HintDb len.

#[global]
Hint Rewrite @singleton_length @length_cons @length_nil : len.
#[global]
Hint Rewrite @length_app @length_drop @length_take @length_fmap
     @length_replicate @repeat_length @subslice_length' : len.
#[global]
Hint Rewrite @length_vec_to_list : len.
#[global]
Hint Rewrite @length_insert : len.
#[global]
Hint Rewrite @length_alter : len.
#[global]
Hint Rewrite u64_le_length : len.
#[global]
Hint Rewrite u32_le_length : len.
#[global]

Ltac len := autorewrite with len; try word; try lia.

Tactic Notation "list_elem" constr(l) constr(i) "as" simple_intropattern(x) :=
  let H := fresh "H" x "_lookup" in
  let i := lazymatch type of i with
           | nat => i
           | Z => constr:(Z.to_nat i)
           | u64 => constr:(uint.nat i)
           end in
  destruct (list_lookup_lt l i) as [x H];
  [ try solve [ len ]
  | ].
