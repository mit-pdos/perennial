From Coq Require Import List.
From stdpp Require Import list vector.
From Perennial.Helpers Require Import Integers.

Lemma singleton_length {A} (x:A) : length [x] = 1%nat.
Proof. reflexivity. Qed.

Lemma length_cons {A} (x:A) xs : length (x::xs) = S (length xs).
Proof. reflexivity. Qed.

Lemma length_nil {A} : length (@nil A) = 0%nat.
Proof. reflexivity. Qed.

Create HintDb len.

#[global]
Hint Rewrite @singleton_length @length_cons @length_nil
  @length_app @length_drop @length_take @length_fmap
  @length_replicate @repeat_length
  @length_insert @length_alter @length_reverse : len.
#[global]
Hint Rewrite @length_vec_to_list : len.
#[global]
Hint Rewrite u64_le_length : len.
#[global]
Hint Rewrite u32_le_length : len.
#[global]
Hint Rewrite length_seqZ : len.

(* users can add their own Hint Unfold's to the len db. *)
(* NOTE: for now, [try lia] is necessary for files
that don't [Require Import Integers].
they run the [word] tactic, but not with the right [solve_unsafe]. *)
Ltac len := autounfold with len; autorewrite with len; try word; try lia.

Tactic Notation "list_elem" constr(l) constr(i) "as" simple_intropattern(x) :=
  let H := fresh "H" x "_lookup" in
  let i := lazymatch type of i with
           | nat => i
           | Z => constr:(Z.to_nat i)
           | u64 => constr:(uint.nat i)
           end in
  destruct (lookup_lt_is_Some_2 l i) as [x H];
  [ try solve [ len ]
  | ].
