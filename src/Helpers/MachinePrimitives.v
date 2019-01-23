(* TODO: this is a bit of a hack, should be using a dedicated Options.v *)
Global Unset Auto Template Polymorphism.
Global Set Implicit Arguments.

From Coq Require Import Omega.
From Coq Require Import Arith.
From Classes Require Import EqualDec.
From stdpp Require Import decidable countable.

Instance eqdecision `{dec:EqualDec A} : EqDecision A := dec.

(** Machine unsigned integers *)

Module UInt.
  Definition max bytes_m1 := pow 2 (8 + 8 * bytes_m1).
  Record t (bytes_m1:nat) :=
    mk { val : nat;
         val_wf : val < max bytes_m1; }.
End UInt.

Arguments UInt.mk bytes_m1 val val_wf : clear implicits.

Definition uint := UInt.t.

Section uint.
  Context {bytes_m1:nat}.
  Notation t := (uint bytes_m1).
  Notation mk := (UInt.mk bytes_m1).
  Notation bound := (UInt.max bytes_m1).

  Implicit Types (x y:t).

  Lemma bound_not_0 : bound <> 0.
  Proof.
    unfold bound.
    apply Nat.pow_nonzero.
    auto.
  Qed.
  Hint Resolve bound_not_0 : core.

  Tactic Notation "mkT" uconstr(x) := refine (mk x _).

  Definition toNum x := x.(UInt.val).

  Definition fromNum (n:nat) : t.
    mkT (n mod bound).
    apply Nat.mod_upper_bound; auto.
  Defined.

  Theorem toNum_inj : forall x y, toNum x = toNum y -> x = y.
  Proof.
    intros.
    destruct x as [x Hx], y as [y Hy]; simpl in *.
    subst; auto.
    f_equal.
    apply proof_irrel.
  Qed.

  Theorem toNum_fromMum : forall n, toNum (fromNum n) = n mod bound.
  Proof.
    unfold toNum, fromNum; simpl; auto.
  Qed.

  Lemma bound_gt_1 : 1 < bound.
  Proof.
    unfold bound.
    change (8 + 8 * bytes_m1) with (1 + (7 + 8 * bytes_m1)).
    rewrite Nat.pow_add_r.
    generalize dependent (7 + 8 * bytes_m1); intros.
    assert (2 ^ n <> 0).
    apply Nat.pow_nonzero; auto.
    generalize dependent (2 ^ n); intros.
    simpl.
    lia.
  Qed.

  Lemma bound_gt_0 : 0 < bound.
    pose proof bound_gt_1.
    lia.
  Qed.

  Hint Resolve bound_gt_0 : core.

  Definition intPlus x y : t.
    mkT ((x.(toNum) + y.(toNum)) mod bound).
    apply Nat.mod_upper_bound; auto.
  Defined.

  Definition intSub x y : t.
    mkT (x.(UInt.val) - y.(UInt.val)).
    pose proof UInt.val_wf x.
    abstract lia.
  Defined.

  Definition int_val0 : t.
    mkT 0.
    auto.
  Defined.

  Definition int_val1 : t.
    mkT 1.
    apply bound_gt_1.
  Defined.

  Definition intCmp x y : comparison :=
    Nat.compare x.(toNum) y.(toNum).

  Global Instance uint_eq_dec : EqualDec t.
  apply (EqualDec.inj_eq_dec toNum toNum_inj).
  Defined.

End uint.

Definition uint64 := UInt.t (8 - 1).
Definition uint32 := UInt.t (4 - 1).
Definition uint16 := UInt.t (2 - 1).
Definition uint8  := UInt.t (1 - 1).

Definition uint_val4096 : uint64 := fromNum 4096.

Definition uint64_to_uint16 (x:uint64) : uint16 :=
  fromNum x.(toNum).

Definition uint64_to_uint32 (x:uint64) : uint32 :=
  fromNum x.(toNum).

Definition upcast_bound {bytes_m1_1 bytes_m1_2} :
  forall x, x < UInt.max bytes_m1_1 ->
       bytes_m1_1 <= bytes_m1_2 ->
       x < UInt.max bytes_m1_2.
Proof.
  intros.
  unfold UInt.max in *.
  eapply Nat.lt_le_trans; eauto.
  apply Nat.pow_le_mono_r; auto.
  lia.
Qed.

Definition uint16_to_uint64 (x:uint16) : uint64.
  refine (UInt.mk _ x.(toNum) _).
  apply (upcast_bound x.(UInt.val_wf)); abstract (simpl; repeat constructor).
Defined.

Definition uint32_to_uint64 (x:uint32) : uint64.
  refine (UInt.mk _ x.(toNum) _).
  apply (upcast_bound x.(UInt.val_wf)); abstract (simpl; repeat constructor).
Defined.

Axiom byte : Type.
Axiom byte_eqdec : EqualDec byte.
Existing Instance byte_eqdec.

Record ByteString :=
  fromByteList { getBytes: list byte }.

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

  Theorem skipn_length A n (l: list A) :
    List.length (List.skipn n l) = List.length l - n.
  Proof.
    generalize dependent n.
    induction l; simpl; intros.
    rewrite skipn_nil; simpl.
    lia.
    destruct n; simpl; auto.
  Qed.

  Theorem drop_length : forall n bs, BS.length (BS.drop n bs) = intSub (BS.length bs) n.
  Proof.
    destruct n as [n ?], bs as [bs].
    apply toNum_inj.
    unfold drop, length, intSub.
    rewrite toNum_fromMum.
    cbn [UInt.val getBytes toNum].
    rewrite toNum_fromMum.
    rewrite skipn_length.
  Admitted.
End BS.

Module BSNotations.
  Delimit Scope bs_scope with bs.
  Infix "++" := BS.append : bs_scope.
End BSNotations.

Class UIntEncoding bytes_m1 : Type :=
  { encodeLE : UInt.t bytes_m1 -> ByteString;
    decodeLE : ByteString -> option (UInt.t bytes_m1);
    encode_length_ok : forall x, toNum (BS.length (encodeLE x)) = 1 + bytes_m1;
    encode_decode_LE_ok : forall x, decodeLE (encodeLE x) = Some x;
  }.

Axiom uint64_le_enc : UIntEncoding (8 - 1).
Axiom uint32_le_enc : UIntEncoding (4 - 1).
Axiom uint16_le_enc : UIntEncoding (2 - 1).
Axiom uint8_le_enc : UIntEncoding (1 - 1).
Existing Instances uint64_le_enc uint32_le_enc uint16_le_enc uint8_le_enc.

(** File descriptors *)

Axiom Fd:Type.
Axiom fd_eqdec : EqualDec Fd.
Existing Instance fd_eqdec.
Axiom fd_countable : Countable Fd.
Existing Instance fd_countable.
