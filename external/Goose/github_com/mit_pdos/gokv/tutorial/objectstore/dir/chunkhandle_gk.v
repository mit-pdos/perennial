(* autogenerated from github.com/mit-pdos/gokv/tutorial/objectstore/dir/chunkhandle_gk *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.tchajed.marshal.

Section code.
Context `{ext_ty: ext_types}.

Definition S := struct.decl [
  "Addr" :: uint64T;
  "ContentHash" :: stringT
].

Definition Marshal: val :=
  rec: "Marshal" "c" "prefix" :=
    let: "enc" := ref_to (slice.T byteT) "prefix" in
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (struct.get S "Addr" "c"));;
    let: "contenthashBytes" := StringToBytes (struct.get S "ContentHash" "c") in
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (slice.len "contenthashBytes"));;
    "enc" <-[slice.T byteT] (marshal.WriteBytes (![slice.T byteT] "enc") "contenthashBytes");;
    ![slice.T byteT] "enc".

Definition Unmarshal: val :=
  rec: "Unmarshal" "s" :=
    let: "enc" := ref_to (slice.T byteT) "s" in
    let: "addr" := ref (zero_val uint64T) in
    let: "contentHash" := ref (zero_val stringT) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    "addr" <-[uint64T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: "contentHashLen" := ref (zero_val uint64T) in
    let: "contentHashBytes" := ref (zero_val (slice.T byteT)) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    "contentHashLen" <-[uint64T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadBytesCopy (![slice.T byteT] "enc") (![uint64T] "contentHashLen") in
    "contentHashBytes" <-[slice.T byteT] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    "contentHash" <-[stringT] (StringFromBytes (![slice.T byteT] "contentHashBytes"));;
    (struct.mk S [
       "Addr" ::= ![uint64T] "addr";
       "ContentHash" ::= ![stringT] "contentHash"
     ], ![slice.T byteT] "enc").

End code.
