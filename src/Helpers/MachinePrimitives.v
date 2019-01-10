(* TODO: this is a bit of a hack, should be using a dedicated Options.v *)
Global Unset Auto Template Polymorphism.
Global Set Implicit Arguments.

From Coq Require Import ZArith.ZArith.
Local Open Scope Z.

Axiom ByteString : Type.

(* TODO: make this unsigned *)
Record MachineInt (bits:nat) : Type :=
  { intTy :> Type;
    int_val0 : intTy;
    int_val1 : intTy;
    intPlus : intTy -> intTy -> intTy;
    intSub : intTy -> intTy -> intTy;
    intCmp : intTy -> intTy -> comparison;
    toNum : intTy -> Z;
    toNum_ok : forall x, toNum x < Z.pow 2 (Z.of_nat bits);
    encodeLE : intTy -> ByteString;
    decodeLE : ByteString -> intTy;
    encode_decode_LE_ok : forall x, decodeLE (encodeLE x) = x; }.

Arguments int_val0 {bits int} : rename.
Arguments int_val1 {bits int} : rename.
Arguments intCmp {bits int} : rename.
Arguments intSub {bits int} : rename.

Axiom int64 : MachineInt 64.
Axiom int32 : MachineInt 32.
Axiom int16 : MachineInt 16.
Axiom int8  : MachineInt 8.

Axiom int_val4096 : int64.

Axiom int64_to_int16 : int64 -> int16.
Axiom int16_to_int64 : int16 -> int64.

Module BS.
  Axiom append : ByteString -> ByteString -> ByteString.
  Axiom length : ByteString -> int64.
  (* BS.take n bs ++ BS.drop n bs = bs *)
  Axiom take : int64 -> ByteString -> ByteString.
  Axiom drop : int64 -> ByteString -> ByteString.
  Axiom empty : ByteString.
End BS.

Module BSNotations.
  Delimit Scope bs_scope with bs.
  Infix "++" := BS.append : bs_scope.
End BSNotations.

Axiom Fd:Type.
