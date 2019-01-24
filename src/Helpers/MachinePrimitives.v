(* TODO: this is a bit of a hack, should be using a dedicated Options.v *)
Global Unset Auto Template Polymorphism.
Global Set Implicit Arguments.

From Coq Require Import Omega.
From Coq Require Import Arith.
From Classes Require Import EqualDec.
From stdpp Require Import decidable countable.

Instance eqdecision `{dec:EqualDec A} : EqDecision A := dec.

From Coq Require Import Extraction.

(** Machine unsigned integers *)

Definition uint_max (bits:nat) := pow 2 bits.

Class UIntT (bits:nat) (intTy:Type) :=
  { toNum : intTy -> nat;
    fromNum : nat -> intTy;
    toNum_wf : forall x, toNum x < uint_max bits;
    fromNum_wf : forall n, toNum (fromNum n) = n mod (uint_max bits);
    toNum_inj : forall x y, toNum x = toNum y -> x = y;
    intPlus : intTy -> intTy -> intTy;
    intSub : intTy -> intTy -> intTy;
    intCmp : intTy -> intTy -> comparison; }.

(* TODO: prove this from some correctness conditions in UIntT *)
Instance uint_eq_dec bits intTy (int:UIntT bits intTy) : EqualDec intTy.
Admitted.

Class BitWidth (bits:nat) :=
  { numBytes : nat;
    numBytes_eq : 8 * numBytes = bits;
    bits_gt_0 : 0 < bits; }.

Theorem uint_max_ne0 bits : uint_max bits <> 0.
Proof.
  unfold uint_max.
  apply Nat.pow_nonzero; auto.
Qed.

Theorem uint_max_gt_1 bits {good:BitWidth bits} : 1 < uint_max bits.
Proof.
  unfold uint_max.
  pose proof bits_gt_0.
  destruct bits; simpl; try lia.
  pose proof (Nat.pow_nonzero 2 bits ltac:(auto)).
  lia.
Qed.

Section UInts.
  Context {bits intTy} {int:UIntT bits intTy}.

  Hint Resolve uint_max_ne0 : core.

  Definition int_val0 : intTy := fromNum 0.
  Theorem int_val0_num : toNum int_val0 = 0.
    unfold int_val0.
    rewrite fromNum_wf.
    rewrite Nat.mod_0_l; auto.
  Qed.

  Definition int_val1 : intTy := fromNum 1.
  Theorem int_val1_num {good:BitWidth bits} : toNum int_val1 = 1.
    unfold int_val1.
    rewrite fromNum_wf.
    apply Nat.mod_small.
    apply uint_max_gt_1.
  Qed.
End UInts.

Axioms uint64 uint32 uint16 uint8 : Type.
Axioms
  (uint64_uint : UIntT 64 uint64)
  (uint32_uint : UIntT 32 uint32)
  (uint16_uint : UIntT 16 uint16)
  (uint8_uint : UIntT 8 uint8)
.

Existing Instances uint64_uint uint32_uint uint16_uint uint8_uint.

Ltac mkBitwidth bits :=
  let bytes := eval simpl in (Nat.div bits 8) in
      let bits_m1 := eval simpl in (bits-1) in
      exact (@Build_BitWidth bits bytes eq_refl (Nat.lt_0_succ bits_m1)).

Instance goodwidth_64 : BitWidth _ := ltac:(mkBitwidth 64).
Instance goodwidth_32 : BitWidth _ := ltac:(mkBitwidth 32).
Instance goodwidth_16 : BitWidth _ := ltac:(mkBitwidth 16).
Instance goodwidth_8 : BitWidth _ := ltac:(mkBitwidth 8).

Definition uint_val4096 : uint64 := fromNum 4096.

Definition as_uint `{uint1:UIntT bits1 intTy1} `(uint2:UIntT bits2 intTy2)
           (x:intTy1) : intTy2 := fromNum x.(toNum).
Arguments as_uint {bits1 intTy1 uint1} {bits2} intTy2 {uint2} x.

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

Theorem drop_length : forall n bs, BS.length (BS.drop n bs) = intSub (BS.length bs) n.
Proof.
  destruct bs as [bs].
  unfold BS.drop, BS.length; cbn [getBytes].
  rewrite skipn_length.
Admitted.

Module BSNotations.
  Delimit Scope bs_scope with bs.
  Infix "++" := BS.append : bs_scope.
End BSNotations.

Class UIntEncoding bits (good:BitWidth bits) intTy (int:UIntT bits intTy) :=
  { encodeLE : intTy -> ByteString;
    decodeLE : ByteString -> option intTy;
    encode_length_ok : forall x, toNum (BS.length (encodeLE x)) = numBytes;
    encode_decode_LE_ok : forall x, decodeLE (encodeLE x) = Some x;
  }.

Arguments UIntEncoding {bits good} intTy {int}.

Axioms
  (uint64_le_enc : UIntEncoding uint64)
  (uint32_le_enc : UIntEncoding uint32)
  (uint16_le_enc : UIntEncoding uint16)
  (uint8_le_enc : UIntEncoding uint8).
Existing Instances uint64_le_enc uint32_le_enc uint16_le_enc uint8_le_enc.

(** File descriptors *)

Axiom Fd:Type.
Axiom fd_eqdec : EqualDec Fd.
Existing Instance fd_eqdec.
Axiom fd_countable : Countable Fd.
Existing Instance fd_countable.
