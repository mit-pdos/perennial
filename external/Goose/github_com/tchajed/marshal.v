(* autogenerated from github.com/tchajed/marshal *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

(* Enc is a stateful encoder for a statically-allocated array. *)
Module Enc.
  Definition S := struct.decl [
    "b" :: slice.T byteT;
    "off" :: refT uint64T
  ].
End Enc.

Definition NewEnc: val :=
  rec: "NewEnc" "sz" :=
    struct.mk Enc.S [
      "b" ::= NewSlice byteT "sz";
      "off" ::= ref (zero_val uint64T)
    ].

Definition Enc__PutInt: val :=
  rec: "Enc__PutInt" "enc" "x" :=
    let: "off" := ![uint64T] (struct.get Enc.S "off" "enc") in
    UInt64Put (SliceSkip byteT (struct.get Enc.S "b" "enc") "off") "x";;
    struct.get Enc.S "off" "enc" <-[uint64T] ![uint64T] (struct.get Enc.S "off" "enc") + #8.

Definition Enc__PutInt32: val :=
  rec: "Enc__PutInt32" "enc" "x" :=
    let: "off" := ![uint64T] (struct.get Enc.S "off" "enc") in
    UInt32Put (SliceSkip byteT (struct.get Enc.S "b" "enc") "off") "x";;
    struct.get Enc.S "off" "enc" <-[uint64T] ![uint64T] (struct.get Enc.S "off" "enc") + #4.

Definition Enc__PutInts: val :=
  rec: "Enc__PutInts" "enc" "xs" :=
    ForSlice uint64T <> "x" "xs"
      (Enc__PutInt "enc" "x").

Definition Enc__PutBytes: val :=
  rec: "Enc__PutBytes" "enc" "b" :=
    let: "off" := ![uint64T] (struct.get Enc.S "off" "enc") in
    let: "n" := SliceCopy byteT (SliceSkip byteT (struct.get Enc.S "b" "enc") "off") "b" in
    struct.get Enc.S "off" "enc" <-[uint64T] ![uint64T] (struct.get Enc.S "off" "enc") + "n".

Definition Enc__Finish: val :=
  rec: "Enc__Finish" "enc" :=
    struct.get Enc.S "b" "enc".

(* Dec is a stateful decoder that returns values encoded
   sequentially in a single slice. *)
Module Dec.
  Definition S := struct.decl [
    "b" :: slice.T byteT;
    "off" :: refT uint64T
  ].
End Dec.

Definition NewDec: val :=
  rec: "NewDec" "b" :=
    struct.mk Dec.S [
      "b" ::= "b";
      "off" ::= ref (zero_val uint64T)
    ].

Definition Dec__GetInt: val :=
  rec: "Dec__GetInt" "dec" :=
    let: "off" := ![uint64T] (struct.get Dec.S "off" "dec") in
    struct.get Dec.S "off" "dec" <-[uint64T] ![uint64T] (struct.get Dec.S "off" "dec") + #8;;
    UInt64Get (SliceSkip byteT (struct.get Dec.S "b" "dec") "off").

Definition Dec__GetInt32: val :=
  rec: "Dec__GetInt32" "dec" :=
    let: "off" := ![uint64T] (struct.get Dec.S "off" "dec") in
    struct.get Dec.S "off" "dec" <-[uint64T] ![uint64T] (struct.get Dec.S "off" "dec") + #4;;
    UInt32Get (SliceSkip byteT (struct.get Dec.S "b" "dec") "off").

Definition Dec__GetInts: val :=
  rec: "Dec__GetInts" "dec" "num" :=
    let: "xs" := ref (zero_val (slice.T uint64T)) in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, ![uint64T] "i" < "num"); (λ: <>, "i" <-[uint64T] ![uint64T] "i" + #1) := λ: <>,
      "xs" <-[slice.T uint64T] SliceAppend uint64T (![slice.T uint64T] "xs") (Dec__GetInt "dec");;
      Continue);;
    ![slice.T uint64T] "xs".

Definition Dec__GetBytes: val :=
  rec: "Dec__GetBytes" "dec" "num" :=
    let: "off" := ![uint64T] (struct.get Dec.S "off" "dec") in
    let: "b" := SliceSubslice byteT (struct.get Dec.S "b" "dec") "off" ("off" + "num") in
    struct.get Dec.S "off" "dec" <-[uint64T] ![uint64T] (struct.get Dec.S "off" "dec") + "num";;
    "b".
