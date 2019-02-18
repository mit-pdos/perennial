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

Inductive Uint64CompareSpec x : uint64 -> Type :=
| CompareEq : compare x x = Eq ->
              Uint64CompareSpec x x
| CompareLt : forall y, toNum x < toNum y ->
                   compare x y = Lt ->
                   Uint64CompareSpec x y
| CompareGt : forall y, toNum x > toNum y ->
                   compare x y = Gt ->
                   Uint64CompareSpec x y
.

Definition u64_compare_dec x y : Uint64CompareSpec x y.
Proof.
  destruct_with_eqn (Nat.compare x.(toNum) y.(toNum));
    [ assert (x = y); [ | subst; eapply CompareEq ]
    | eapply CompareLt
    | eapply CompareGt ];
    unfold compare; simpl;
      eauto.
  - apply Nat.compare_eq_iff in Heqc.
    apply toNum_inj; auto.
  - apply Nat.compare_lt_iff in Heqc; auto.
  - apply Nat.compare_gt_iff in Heqc; auto.
Defined.

Definition compare_to_pf {x y c} :
  compare x y = c ->
  match c with
  | Eq => x = y
  | Lt => toNum x < toNum y
  | Gt => toNum x > toNum y
  end.
Proof.
  intros; subst.
  destruct (u64_compare_dec x y);
    rewrite e;
    eauto.
Qed.

Local Definition compare_lt_dec_helper x y :
  {H & equal (compare x y) Lt = left H /\
       toNum x < toNum y} +
  {H & equal (compare x y) Lt = right H /\
       toNum x >= toNum y}.
Proof.
  destruct (u64_compare_dec x y); rewrite e;
    match goal with
    | |- context[equal ?x ?y] => destruct (equal x y); try congruence
    end;
    eauto.
  assert (toNum x >= toNum y) by lia; eauto.
Qed.

Local Definition compare_gt_dec_helper x y :
  {H & equal (compare x y) Gt = left H /\
       toNum x > toNum y} +
  {H & equal (compare x y) Gt = right H /\
       toNum x <= toNum y}.
Proof.
  destruct (u64_compare_dec x y); rewrite e;
    match goal with
    | |- context[equal ?x ?y] => destruct (equal x y); try congruence
    end;
    eauto.
  assert (toNum x <= toNum y) by lia; eauto.
Qed.

Theorem compare_eq x : compare x x = Eq.
Proof.
  destruct x; simpl.
  apply Nat.compare_eq_iff; auto.
Qed.

Inductive BinaryCompareSpec (x y : uint64) (c:comparison)
          (Peq Pneq: Prop) :=
| CompareIsEq Heq (Hc: equal (compare x y) c = left Heq) (pf:Peq)
| CompareIsNeq Hneq (Hc: equal (compare x y) c = right Hneq) (pf:Pneq).

Definition compare_lt_dec x y :
  BinaryCompareSpec x y Lt
                    (toNum x < toNum y)
                    (toNum x >= toNum y).
Proof.
  destruct (compare_lt_dec_helper x y).
  destruct s; intuition; eauto using BinaryCompareSpec.
  destruct s; intuition; eauto using BinaryCompareSpec.
Qed.

Definition compare_gt_dec x y :
  BinaryCompareSpec x y Gt
                    (toNum x > toNum y)
                    (toNum x <= toNum y).
Proof.
  destruct (compare_gt_dec_helper x y).
  destruct s; intuition; eauto using BinaryCompareSpec.
  destruct s; intuition; eauto using BinaryCompareSpec.
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
Declare Instance byte_eqdec : EqualDec byte.

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
  Definition concat (bss: list ByteString) := fromByteList (concat (map getBytes bss)).
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

Module BSNotations.
  Delimit Scope bs_scope with bs.
  Infix "++" := BS.append : bs_scope.
End BSNotations.

Section ByteStringProperties.
  Ltac start :=
    repeat match goal with
           | [ a: uint64 |- _ ] => destruct a as [a]
           | [ bs: ByteString |- _ ] => destruct bs as [bs]
           | |- @eq uint64 _ _ => apply toNum_inj
           | |- @eq ByteString _ _ => apply getBytes_inj
           | _ => progress simpl
           | |- forall _, _ => intros
           end.

  Import UIntNotations.
  Import BSNotations.

  Local Open Scope u64.
  Local Open Scope bs.

  Theorem append_assoc bs1 bs2 bs3 :
    (bs1 ++ bs2) ++ bs3 = bs1 ++ bs2 ++ bs3.
  Proof.
    start.
    rewrite app_assoc; auto.
  Qed.

  Theorem drop_length : forall n bs, BS.length (BS.drop n bs) = BS.length bs - n.
  Proof.
    start.
    rewrite skipn_length.
    reflexivity.
  Qed.

  Theorem drop_drop n m bs :
    BS.drop n (BS.drop m bs) = BS.drop (m + n) bs.
  Proof.
    start.
    rewrite list.drop_drop; auto.
  Qed.

  Theorem drop_app_exact n bs1 bs2 :
    n = BS.length bs1 ->
    BS.drop n (bs1 ++ bs2) = bs2.
  Proof.
    intros ->.
    start.
    rewrite list.drop_app; auto.
  Qed.

  Theorem app_length bs1 bs2 :
    BS.length (bs1 ++ bs2) = BS.length bs1 + BS.length bs2.
  Proof.
    start.
    rewrite app_length; auto.
  Qed.

  Theorem app_empty bs :
    BS.append BS.empty bs = bs.
  Proof.
    start; eauto.
  Qed.

  Theorem take_app_exact n bs1 bs2 :
    BS.length bs1 = n ->
    BS.take n (bs1 ++ bs2) = bs1.
  Proof.
    start.
    apply fromNum_inj in H; subst; simpl.
    rewrite take_app; auto.
  Qed.

  Theorem take_app_first n bs1 bs2 :
    n.(toNum) <= (BS.length bs1).(toNum) ->
    BS.take n (bs1 ++ bs2) = BS.take n bs1.
  Proof.
    start.
    rewrite take_app_le; eauto.
  Qed.

  Theorem take_app_second n bs1 bs2 :
    n.(toNum) >= (BS.length bs1).(toNum) ->
    BS.take n (bs1 ++ bs2) = bs1 ++ BS.take (n - BS.length bs1) bs2.
  Proof.
    start.
    rewrite take_app_ge; eauto.
  Qed.

  Theorem take_length_le bs n :
    toNum n <= toNum (BS.length bs) ->
    BS.length (BS.take n bs) = n.
  Proof.
    start.
    rewrite take_length.
    lia.
  Qed.

  Theorem take_length_gt bs n :
    toNum n > toNum (BS.length bs) ->
    BS.length (BS.take n bs) = BS.length bs.
  Proof.
    start.
    rewrite take_length.
    lia.
  Qed.

  Theorem take_take1 bs n m :
    n.(toNum) <= m.(toNum) ->
    BS.take n (BS.take m bs) = BS.take n bs.
  Proof.
    start.
    rewrite take_take.
    f_equal; lia.
  Qed.

  Theorem take_take2 bs n m :
    m.(toNum) <= n.(toNum) ->
    BS.take n (BS.take m bs) = BS.take m bs.
  Proof.
    start.
    rewrite take_take.
    f_equal; lia.
  Qed.

End ByteStringProperties.

Record LittleEndianEncoder bytes intTy (enc:intTy -> ByteString) (dec:ByteString -> option intTy) :=
  { encode_length_ok : forall x, BS.length (enc x) = fromNum bytes;
    encode_decode_ok : forall x, dec (enc x) = Some x; }.

Axiom uint64_to_le : uint64 -> ByteString.
Axiom uint64_from_le : ByteString -> option uint64.

Axiom uint64_le_enc : LittleEndianEncoder 8 uint64_to_le uint64_from_le.

(** File descriptors *)

Axiom Fd:Type.
(* needed to model zero-valued structs *)
(* TODO: need to make sure normal fds are not equal to InvalidFd *)
Axiom InvalidFd:Fd.
Declare Instance fd_eqdec : EqualDec Fd.
Declare Instance fd_countable : Countable Fd.
