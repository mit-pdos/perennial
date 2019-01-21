(* TODO: this is a bit of a hack, should be using a dedicated Options.v *)
Global Unset Auto Template Polymorphism.
Global Set Implicit Arguments.

From Classes Require Import EqualDec.

From stdpp Require Import decidable countable.

Instance eqdecision `{dec:EqualDec A} : EqDecision A := dec.

From Coq Require Import NArith.NArith.
Local Open Scope N.

Axiom ByteString : Type.
Axiom eqdec_ByteString : EqualDec ByteString.
Existing Instance eqdec_ByteString.

Record MachineUint (bits:nat) : Type :=
  { intTy :> Type;
    intPlus : intTy -> intTy -> intTy;
    intSub : intTy -> intTy -> intTy;
    intCmp : intTy -> intTy -> comparison;
    fromNum : N -> intTy;
    toNum : intTy -> N;
    toNum_ok : forall x, toNum x < N.pow 2 (N.of_nat bits);
    encodeLE : intTy -> ByteString;
    decodeLE : ByteString -> intTy;
    encode_decode_LE_ok : forall x, decodeLE (encodeLE x) = x; }.

Definition int_val0 bits {int:MachineUint bits} := int.(fromNum) 0.
Definition int_val1 bits {int:MachineUint bits} := int.(fromNum) 1.
Arguments intCmp {bits int} : rename.
Arguments intSub {bits int} : rename.

Axiom uint64 : MachineUint 64.
Axiom uint32 : MachineUint 32.
Axiom uint16 : MachineUint 16.
Axiom uint8   : MachineUint 8.

Definition uint_val4096 : uint64 := uint64.(fromNum) 4096.

Axiom uint64_to_uint16 : uint64 -> uint16.
Axiom uint64_to_uint32 : uint64 -> uint32.
Axiom uint16_to_uint64 : uint16 -> uint64.
Axiom uint32_to_uint64 : uint32 -> uint64.

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

Axiom Fd:Type.
Axiom fd_eqdec : EqualDec Fd.
Existing Instance fd_eqdec.
Axiom fd_countable : Countable Fd.
Existing Instance fd_countable.
