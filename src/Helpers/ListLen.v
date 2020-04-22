From Coq Require Import List.
From stdpp Require Import list vector.
From Perennial.Helpers Require Import Integers.

Hint Rewrite app_length @drop_length @take_length @fmap_length
     @replicate_length : len.
Hint Rewrite @vec_to_list_length : len.
Hint Rewrite @insert_length : len.
Hint Rewrite u64_le_length : len.

Ltac len := autorewrite with len; try word.
