(* autogenerated from github.com/mit-pdos/gokv/tutorial/objectstore/dir/recordchunk_gk *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.tchajed.marshal.

Section code.
Context `{ext_ty: ext_types}.

Definition S := struct.decl [
  "WriteId" :: uint64T;
  "Server" :: uint64T;
  "ContentHash" :: stringT;
  "Index" :: uint64T
].

Definition Marshal: val :=
  rec: "Marshal" "r" "prefix" :=
    let: "enc" := ref_to (slice.T byteT) "prefix" in
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (struct.get S "WriteId" "r"));;
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (struct.get S "Server" "r"));;
    let: "contenthashBytes" := StringToBytes (struct.get S "ContentHash" "r") in
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (slice.len "contenthashBytes"));;
    "enc" <-[slice.T byteT] (marshal.WriteBytes (![slice.T byteT] "enc") "contenthashBytes");;
    "enc" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "enc") (struct.get S "Index" "r"));;
    ![slice.T byteT] "enc".

Definition Unmarshal: val :=
  rec: "Unmarshal" "s" :=
    let: "enc" := ref_to (slice.T byteT) "s" in
    let: "writeId" := ref (zero_val uint64T) in
    let: "server" := ref (zero_val uint64T) in
    let: "contentHash" := ref (zero_val stringT) in
    let: "index" := ref (zero_val uint64T) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    "writeId" <-[uint64T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    "server" <-[uint64T] "0_ret";;
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
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "enc") in
    "index" <-[uint64T] "0_ret";;
    "enc" <-[slice.T byteT] "1_ret";;
    (struct.mk S [
       "WriteId" ::= ![uint64T] "writeId";
       "Server" ::= ![uint64T] "server";
       "ContentHash" ::= ![stringT] "contentHash";
       "Index" ::= ![uint64T] "index"
     ], ![slice.T byteT] "enc").

End code.
