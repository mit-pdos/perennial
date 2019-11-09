From Coq Require Export BinNat.

From stdpp Require Import decidable countable.
(* TODO: replace bbv.Word with coqutil.Word *)
From bbv Require Import Word.

Open Scope N_scope.

(* this is sort of a big number *)
Definition n64: nat := 64.
Notation u64 := (word n64).

(* TODO: to make minimal changes to heap_lang we use Z as the "model" for
integers in several places; these should be replaced by u64 itself where
possible and N elsewhere. *)
Definition u64_Z (x:u64) : Z :=
  Z.of_N (Word.wordToN x).

Set Printing Coercions.

Theorem u64_Z_through_nat : forall (x:u64), Z.of_nat (Word.wordToNat x) = u64_Z x.
Proof.
  unfold u64_Z; intros.
  rewrite Word.wordToN_nat.
  rewrite nat_N_Z; auto.
Qed.

Theorem u64_nat_through_Z : forall (x:u64), Z.to_nat (u64_Z x) = Word.wordToNat x.
Proof.
  unfold u64_Z; intros.
  rewrite N_Z_nat_conversions.N_to_Z_to_nat.
  rewrite Word.wordToN_to_nat; auto.
Qed.

Unset Printing Coercions.

Instance word_eq_dec sz : EqDecision (word sz) := @weq sz.
Instance word_countable sz : Countable (word sz).
Proof.
  apply (inj_countable
           (@wordToN sz)
           (fun n => Some (NToWord sz n))); intros.
  by rewrite NToWord_wordToN.
Qed.

Instance wlt_decide sz : Decision (@wlt sz x y) := @wlt_dec sz.

Definition byte := (word 8).

(* we don't actually do anything with a byte except use its zero value and
encode integers into bytes, so nothing operates on bytes for now. *)

(* TODO: all of this is provided by coqutil (using a length-indexed tuple for
   the bytes) *)

Definition u32_le (x:word 32) : list byte :=
  let (b1, x) := (@split1 8 24 x, @split2 8 24 x) in
  let (b2, x) := (@split1 8 16 x, @split2 8 16 x) in
  let (b3, b4) := (@split1 8 8 x, @split2 8 8 x) in
  [b4;b3;b2;b1].

Fixpoint mul' (n m:nat) :=
  match n with
  | O => 0
  | S n => mul' n m + m
  end%nat.

Fixpoint le_to_word (l: list byte) : word (mul' (length l) 8).
  destruct l.
  - exact WO.
  - exact (Word.combine (le_to_word l) b).
Defined.

Theorem u32_le_to_word : forall x,
    le_to_word (u32_le x) = x.
Proof.
Admitted.

Definition u64_le (x:u64) : list byte :=
  let (h32, l32) := (@split1 32 32 x, @split2 32 32 x) in
  let (h, l) := (u32_le h32, u32_le l32) in
  l ++ h.

Theorem u64_le_to_word : forall x,
    le_to_word (u64_le x) = x.
Proof.
Admitted.
