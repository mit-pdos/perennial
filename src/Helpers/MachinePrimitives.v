(* TODO: this is a bit of a hack, should be using a dedicated Options.v *)
Global Unset Auto Template Polymorphism.
Global Set Implicit Arguments.

From Classes Require Import EqualDec.

From stdpp Require Import decidable countable.

Instance eqdecision `{dec:EqualDec A} : EqDecision A := dec.

From Coq Require Import NArith.NArith.
Local Open Scope N.

(** Machine unsigned integers *)

Record MachineUInt (bytes:nat) : Type :=
  { intTy :> Type;
    intPlus : intTy -> intTy -> intTy;
    intSub : intTy -> intTy -> intTy;
    intCmp : intTy -> intTy -> comparison;
    fromNum : N -> intTy;
    int_val0 := fromNum 0;
    int_val1 := fromNum 1;
    toNum : intTy -> N;
    toNum_inj : forall x y, toNum x = toNum y -> x = y;
    intCmp_ok : forall x y, intCmp x y = N.compare (toNum x) (toNum y);
    toNum_ok : forall x, toNum x < N.pow 2 (8 * N.of_nat bytes);
  }.

Arguments int_val0 {bytes int} : rename.
Arguments int_val1 {bytes int} : rename.
Arguments intCmp {bytes int} : rename.
Arguments intSub {bytes int} : rename.
Arguments toNum {bytes int} : rename.

Instance uint_eqdec bytes (int: MachineUInt bytes) : EqualDec int.
Proof.
  hnf; intros.
  destruct_with_eqn (intCmp x y);
    [ left | right; intros -> .. ];
    rewrite intCmp_ok, ?N.compare_eq_iff, ?N.compare_refl in *.
  - auto using toNum_inj.
  - congruence.
  - congruence.
Defined.

Axiom uint64 : MachineUInt 8.
Axiom uint32 : MachineUInt 4.
Axiom uint16 : MachineUInt 2.
Axiom uint8  : MachineUInt 1.

Definition uint_val4096 : uint64 := uint64.(fromNum) 4096.

Axiom uint64_to_uint16 : uint64 -> uint16.
Axiom uint64_to_uint32 : uint64 -> uint32.
Axiom uint16_to_uint64 : uint16 -> uint64.
Axiom uint32_to_uint64 : uint32 -> uint64.

Axiom ByteString : Type.
Axiom eqdec_ByteString : EqualDec ByteString.
Existing Instance eqdec_ByteString.

Module BS.
  Axiom append : ByteString -> ByteString -> ByteString.
  Axiom length : ByteString -> uint64.
  (* BS.take n bs ++ BS.drop n bs = bs *)
  Axiom take : uint64 -> ByteString -> ByteString.
  Axiom drop : uint64 -> ByteString -> ByteString.
  Axiom empty : ByteString.

  (* TODO: probably best derived from other axioms *)
  Axiom drop_length : forall n bs, BS.length (BS.drop n bs) = intSub (BS.length bs) n.
End BS.

Module BSNotations.
  Delimit Scope bs_scope with bs.
  Infix "++" := BS.append : bs_scope.
End BSNotations.

Class UIntEncoding bytes (int: MachineUInt bytes) : Type :=
  { encodeLE : int -> ByteString;
    decodeLE : ByteString -> option int;
    encode_length_ok : forall x, toNum (BS.length (encodeLE x)) = N.of_nat bytes;
    encode_decode_LE_ok : forall x, decodeLE (encodeLE x) = Some x;
  }.

Axiom uint64_le_enc : UIntEncoding uint64.
Axiom uint32_le_enc : UIntEncoding uint32.
Axiom uint16_le_enc : UIntEncoding uint16.
Axiom uint8_le_enc : UIntEncoding uint8.
Existing Instances uint64_le_enc uint32_le_enc uint16_le_enc uint8_le_enc.

(** File descriptors *)

Axiom Fd:Type.
Axiom fd_eqdec : EqualDec Fd.
Existing Instance fd_eqdec.
Axiom fd_countable : Countable Fd.
Existing Instance fd_countable.
