From Coq Require Import List.
From stdpp Require Import list vector.
From Perennial.Helpers Require Import Integers.

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

Ltac len := autorewrite with len; try word.
