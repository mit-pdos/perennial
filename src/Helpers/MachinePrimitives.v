Set Implicit Arguments.

From Coq Require Import Omega.
From Coq Require Import Arith.
From Classes Require Import EqualDec.
From stdpp Require Import decidable countable.

Instance eqdecision `{dec:EqualDec A} : EqDecision A := dec.

From Coq Require Import Extraction.

(** Machine unsigned integers *)

(* These will extract to Word64, with checked arithmetic to ensure the program
raises an exception (that is, crashes) if it overflows, leaving the model. We
can handle underflow by returning 0; we have to check anyway and the Coq model
saturates to 0 so we might as well match it (relying on this is a bad idea in
case we ever make this situation better). *)
Record uint64 : Type :=
  fromNum { toNum : nat }.

(* so convenient! wow! *)
Coercion fromNum : nat >-> uint64.

Lemma toNum_inj : forall x y, toNum x = toNum y -> x = y.
Proof.
  destruct x, y; simpl; auto.
Qed.

Lemma from_to_num_id : forall x, fromNum (toNum x) = x.
Proof.
  destruct x; simpl; auto.
Qed.

Lemma to_from_num_id : forall n, toNum (fromNum n) = n.
Proof.
  simpl; auto.
Qed.

Lemma u64_neq n m :
    fromNum n <> fromNum m ->
    n <> m.
Proof.
  intuition auto.
Qed.

Lemma fromNum_inj n m :
    fromNum n = fromNum m ->
    n = m.
Proof.
  inversion 1; auto.
Qed.

Ltac u64_cleanup :=
  repeat match goal with
         | [ H: fromNum ?n = fromNum ?m |- _ ] =>
           apply fromNum_inj in H
         | [ H: fromNum ?n <> fromNum ?m |- _ ] =>
           apply u64_neq in H
         end.

Section UInt64.
  Implicit Types (x y:uint64).
  Definition add x y : uint64 := fromNum (x.(toNum) + y.(toNum)).
  Definition sub x y : uint64 := fromNum (x.(toNum) - y.(toNum)).
  Definition compare x y : comparison := Nat.compare x.(toNum) y.(toNum).
End UInt64.

Instance uint64_eq_dec : EqualDec uint64.
Proof.
  hnf; intros.
  destruct_with_eqn (compare x y); unfold compare in *;
    [ left | right; intros <- .. ].
  - destruct x as [x], y as [y]; simpl in *.
    apply Nat.compare_eq_iff in Heqc; auto using toNum_inj.
  - destruct x as [x]; simpl in *.
    rewrite Nat.compare_refl in *; congruence.
  - destruct x as [x]; simpl in *.
    rewrite Nat.compare_refl in *; congruence.
Defined.

Instance uint64_countable : Countable uint64.
Proof.
  refine {| encode x := Pos.of_nat (S (toNum x));
            decode n := Some (fromNum (Pos.to_nat n - 1)) |}.
  intros.
  destruct x as [x].
  rewrite Nat2Pos.id; simpl; try lia.
  rewrite Nat.sub_0_r; auto.
Qed.

Definition four_kilobytes : uint64 := fromNum 4096.

Module UIntNotations.
  Delimit Scope uint64_scope with u64.
  Infix "+" := add : uint64_scope.
  Infix "-" := sub : uint64_scope.
  Notation "0" := (fromNum 0) : uint64_scope.
  Notation "1" := (fromNum 1) : uint64_scope.
  Notation "4096" := four_kilobytes : uint64_scope.
End UIntNotations.

Section UInt64Properties.
  Implicit Types (x y z:uint64).
  Import UIntNotations.
  Local Open Scope u64.

  Set Printing Coercions.

  Ltac start :=
    repeat match goal with
           | |- forall _, _ => intros
           | [ a: uint64 |- _ ] => destruct a as [a]
           | |- @eq uint64 _ _ => apply toNum_inj
           end; simpl;
    try lia.

  Theorem add_comm x y : x + y = y + x.
  Proof.
    start.
  Qed.

  Theorem add_assoc x y z : x + (y + z) = x + y + z.
  Proof.
    start.
  Qed.
End UInt64Properties.

(* bytes are completely opaque; there should be no need to worry about them *)
Axiom byte : Type.
Axiom byte_eqdec : EqualDec byte.
Existing Instance byte_eqdec.

Record ByteString :=
  fromByteList { getBytes: list byte }.

Local Theorem getBytes_inj bs1 bs2 :
  getBytes bs1 = getBytes bs2 -> bs1 = bs2.
Proof.
  destruct bs1, bs2; simpl.
  intros ->; auto.
Qed.

Instance ByteString_eq_dec : EqualDec ByteString.
Proof.
  hnf; decide equality.
  apply (equal getBytes0 getBytes1).
Defined.

Module BS.
  Implicit Types (bs:ByteString).
  Local Coercion getBytes : ByteString >-> list.
  Definition append bs1 bs2 := fromByteList (bs1 ++ bs2).
  Definition length bs : uint64 := fromNum (List.length bs).
  Definition take (n:uint64) bs :=
    fromByteList (List.firstn n.(toNum) bs).
  Definition drop (n:uint64) bs :=
    fromByteList (List.skipn n.(toNum) bs).
  Definition empty : ByteString := fromByteList [].
  (* argh, we actually do need conversions between strings and ByteStrings
because of paths; maybe we should write the entire filesystem API in terms of
ByteString paths? It might even be easier than these conversions; the only
problem perhaps will be a handful of string literals. We really don't want to
use string as the ByteString model since it lacks all the theorems about
lists. *)
  Axiom fromString : String.string -> ByteString.
  Axiom toString : ByteString -> String.string.
End BS.

Lemma skipn_nil A n : skipn n (@nil A) = nil.
  induction n; simpl; auto.
Qed.

Lemma skipn_length A n (l: list A) :
  List.length (List.skipn n l) = List.length l - n.
Proof.
  generalize dependent n.
  induction l; simpl; intros.
  rewrite skipn_nil; simpl.
  lia.
  destruct n; simpl; auto.
Qed.

Section ByteStringProperties.
  Ltac start :=
    repeat match goal with
           | |- forall _, _ => intros
           | [ a: uint64 |- _ ] => destruct a as [a]
           | [ bs: ByteString |- _ ] => destruct bs as [bs]
           | |- @eq uint64 _ _ => apply toNum_inj
           | |- @eq ByteString _ _ => apply getBytes_inj
           end; simpl.

  Import UIntNotations.

  Theorem drop_length : forall n bs, BS.length (BS.drop n bs) = (BS.length bs - n)%u64.
  Proof.
    start.
    rewrite skipn_length.
    reflexivity.
  Qed.

  Theorem drop_drop n m bs :
    BS.drop n (BS.drop m bs) = BS.drop (m + n)%u64 bs.
  Proof.
    start.
    rewrite list.drop_drop; auto.
  Qed.
End ByteStringProperties.

Module BSNotations.
  Delimit Scope bs_scope with bs.
  Infix "++" := BS.append : bs_scope.
End BSNotations.

Class LittleEndianEncoder intTy :=
  { encodeLE : intTy -> ByteString;
    decodeLE : ByteString -> option intTy; }.

Class LittleEndianEncoderOK bytes intTy (enc:LittleEndianEncoder intTy) :=
  { encode_length_ok : forall x, toNum (BS.length (encodeLE x)) = bytes;
    encode_decode_LE_ok : forall x, decodeLE (encodeLE x) = Some x; }.

Axiom uint64_to_le : uint64 -> ByteString.
Axiom uint64_from_le : ByteString -> option uint64.

Instance uint64_le_enc : LittleEndianEncoder uint64 :=
  {| encodeLE := uint64_to_le;
     decodeLE := uint64_from_le; |}.

Axiom uint64_enc_ok : LittleEndianEncoderOK 8 uint64_le_enc.
Existing Instance uint64_enc_ok.

(** File descriptors *)

Axiom Fd:Type.
Axiom fd_eqdec : EqualDec Fd.
Existing Instance fd_eqdec.
Axiom fd_countable : Countable Fd.
Existing Instance fd_countable.
