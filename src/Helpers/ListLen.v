From Coq Require Import List.
From stdpp Require Import list vector.
From Perennial.Helpers Require Import List Integers.

Lemma singleton_length {A} (x:A) : length [x] = 1%nat.
Proof. reflexivity. Qed.

Lemma cons_length {A} (x:A) xs : length (x::xs) = S (length xs).
Proof. reflexivity. Qed.

Lemma nil_length {A} : length (@nil A) = 0%nat.
Proof. reflexivity. Qed.

Hint Rewrite @singleton_length @cons_length @nil_length : len.
Hint Rewrite app_length @drop_length @take_length @fmap_length
     @replicate_length : len.
Hint Rewrite @vec_to_list_length : len.
Hint Rewrite @insert_length : len.
Hint Rewrite u64_le_length : len.
Hint Rewrite u32_le_length : len.

Ltac len := autorewrite with len; try word.

Tactic Notation "list_elem" constr(l) constr(i) "as" simple_intropattern(x) :=
  let H := fresh "H" x "_lookup" in
  let i := lazymatch type of i with
           | nat => i
           | Z => constr:(Z.to_nat i)
           | u64 => constr:(int.nat i)
           end in
  destruct (list_lookup_lt _ l i) as [x H];
  [ try solve [ len ]
  | ].
