(* autogenerated from github.com/mit-pdos/gokv/tutorial/kvservice *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.
From Goose Require github_com.mit_pdos.gokv.urpc.
From Goose Require github_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* client.go *)

Definition Clerk := struct.decl [
  "rpcCl" :: ptrT
].

Definition Locked := struct.decl [
  "rpcCl" :: ptrT;
  "id" :: uint64T
].

(* Client from kvservice_rpc.gb.go *)

Definition Client := struct.decl [
  "cl" :: ptrT
].

Definition makeClient: val :=
  rec: "makeClient" "hostname" :=
    struct.new Client [
      "cl" ::= urpc.MakeClient "hostname"
    ].

Definition MakeClerk: val :=
  rec: "MakeClerk" "host" :=
    struct.new Clerk [
      "rpcCl" ::= makeClient "host"
    ].

Definition rpcIdGetFreshNum : expr := #0.

Definition rpcIdPut : expr := #1.

Definition rpcIdConditionalPut : expr := #2.

Definition rpcIdGet : expr := #3.

(* DecodeUint64 from kvservice.gb.go *)

Definition DecodeUint64: val :=
  rec: "DecodeUint64" "x" :=
    let: ("a", <>) := marshal.ReadInt "x" in
    "a".

(* Client__getFreshNumRpc from kvservice_rpc.gb.go *)

Definition Client__getFreshNumRpc: val :=
  rec: "Client__getFreshNumRpc" "cl" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "err" := urpc.Client__Call (struct.loadF Client "cl" "cl") rpcIdGetFreshNum (NewSlice byteT #0) "reply" #100 in
    (if: ("err" = urpc.ErrNone)
    then (DecodeUint64 (![slice.T byteT] "reply"), "err")
    else (#0, "err")).

(* putArgs from kvservice.gb.go *)

(* Put *)
Definition putArgs := struct.decl [
  "opId" :: uint64T;
  "key" :: stringT;
  "val" :: stringT
].

Definition encodePutArgs: val :=
  rec: "encodePutArgs" "a" :=
    let: "e" := ref_to (slice.T byteT) (NewSlice byteT #0) in
    "e" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "e") (struct.loadF putArgs "opId" "a");;
    let: "keyBytes" := Data.stringToBytes (struct.loadF putArgs "key" "a") in
    "e" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "e") (slice.len "keyBytes");;
    "e" <-[slice.T byteT] marshal.WriteBytes (![slice.T byteT] "e") "keyBytes";;
    "e" <-[slice.T byteT] marshal.WriteBytes (![slice.T byteT] "e") (Data.stringToBytes (struct.loadF putArgs "val" "a"));;
    ![slice.T byteT] "e".

(* Client__putRpc from kvservice_rpc.gb.go *)

Definition Client__putRpc: val :=
  rec: "Client__putRpc" "cl" "args" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "err" := urpc.Client__Call (struct.loadF Client "cl" "cl") rpcIdPut (encodePutArgs "args") "reply" #100 in
    (if: ("err" = urpc.ErrNone)
    then "err"
    else "err").

Definition Clerk__Put: val :=
  rec: "Clerk__Put" "ck" "key" "val" :=
    let: "err" := ref (zero_val uint64T) in
    let: "opId" := ref (zero_val uint64T) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: ("0_ret", "1_ret") := Client__getFreshNumRpc (struct.loadF Clerk "rpcCl" "ck") in
      "opId" <-[uint64T] "0_ret";;
      "err" <-[uint64T] "1_ret";;
      (if: (![uint64T] "err" = #0)
      then Break
      else Continue));;
    let: "args" := struct.new putArgs [
      "opId" ::= ![uint64T] "opId";
      "key" ::= "key";
      "val" ::= "val"
    ] in
    Skip;;
    (for: (λ: <>, Client__putRpc (struct.loadF Clerk "rpcCl" "ck") "args" ≠ urpc.ErrNone); (λ: <>, Skip) := λ: <>,
      Continue);;
    #().

(* conditionalPutArgs from kvservice.gb.go *)

(* ConditionalPut *)
Definition conditionalPutArgs := struct.decl [
  "opId" :: uint64T;
  "key" :: stringT;
  "expectedVal" :: stringT;
  "newVal" :: stringT
].

Definition encodeConditionalPutArgs: val :=
  rec: "encodeConditionalPutArgs" "a" :=
    let: "e" := ref_to (slice.T byteT) (NewSlice byteT #0) in
    "e" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "e") (struct.loadF conditionalPutArgs "opId" "a");;
    let: "keyBytes" := Data.stringToBytes (struct.loadF conditionalPutArgs "key" "a") in
    "e" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "e") (slice.len "keyBytes");;
    "e" <-[slice.T byteT] marshal.WriteBytes (![slice.T byteT] "e") "keyBytes";;
    let: "expectedValBytes" := Data.stringToBytes (struct.loadF conditionalPutArgs "expectedVal" "a") in
    "e" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "e") (slice.len "expectedValBytes");;
    "e" <-[slice.T byteT] marshal.WriteBytes (![slice.T byteT] "e") "expectedValBytes";;
    "e" <-[slice.T byteT] marshal.WriteBytes (![slice.T byteT] "e") (Data.stringToBytes (struct.loadF conditionalPutArgs "newVal" "a"));;
    ![slice.T byteT] "e".

(* Client__conditionalPutRpc from kvservice_rpc.gb.go *)

Definition Client__conditionalPutRpc: val :=
  rec: "Client__conditionalPutRpc" "cl" "args" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "err" := urpc.Client__Call (struct.loadF Client "cl" "cl") rpcIdConditionalPut (encodeConditionalPutArgs "args") "reply" #100 in
    (if: ("err" = urpc.ErrNone)
    then (Data.bytesToString (![slice.T byteT] "reply"), "err")
    else (#(str""), "err")).

(* returns true if ConditionalPut was successful, false if current value did not
   match expected value. *)
Definition Clerk__ConditionalPut: val :=
  rec: "Clerk__ConditionalPut" "ck" "key" "expectedVal" "newVal" :=
    let: "err" := ref (zero_val uint64T) in
    let: "opId" := ref (zero_val uint64T) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: ("0_ret", "1_ret") := Client__getFreshNumRpc (struct.loadF Clerk "rpcCl" "ck") in
      "opId" <-[uint64T] "0_ret";;
      "err" <-[uint64T] "1_ret";;
      (if: (![uint64T] "err" = #0)
      then Break
      else Continue));;
    let: "args" := struct.new conditionalPutArgs [
      "opId" ::= ![uint64T] "opId";
      "key" ::= "key";
      "expectedVal" ::= "expectedVal";
      "newVal" ::= "newVal"
    ] in
    let: "ret" := ref (zero_val boolT) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: ("reply", "err") := Client__conditionalPutRpc (struct.loadF Clerk "rpcCl" "ck") "args" in
      (if: ("err" = urpc.ErrNone)
      then
        "ret" <-[boolT] ("reply" = #(str"ok"));;
        Break
      else Continue));;
    ![boolT] "ret".

(* getArgs from kvservice.gb.go *)

(* Get *)
Definition getArgs := struct.decl [
  "opId" :: uint64T;
  "key" :: stringT
].

Definition encodeGetArgs: val :=
  rec: "encodeGetArgs" "a" :=
    let: "e" := ref_to (slice.T byteT) (NewSlice byteT #0) in
    "e" <-[slice.T byteT] marshal.WriteInt (![slice.T byteT] "e") (struct.loadF getArgs "opId" "a");;
    "e" <-[slice.T byteT] marshal.WriteBytes (![slice.T byteT] "e") (Data.stringToBytes (struct.loadF getArgs "key" "a"));;
    ![slice.T byteT] "e".

(* Client__getRpc from kvservice_rpc.gb.go *)

Definition Client__getRpc: val :=
  rec: "Client__getRpc" "cl" "args" :=
    let: "reply" := ref (zero_val (slice.T byteT)) in
    let: "err" := urpc.Client__Call (struct.loadF Client "cl" "cl") rpcIdGet (encodeGetArgs "args") "reply" #100 in
    (if: ("err" = urpc.ErrNone)
    then (Data.bytesToString (![slice.T byteT] "reply"), "err")
    else (#(str""), "err")).

(* returns true if ConditionalPut was successful, false if current value did not
   match expected value. *)
Definition Clerk__Get: val :=
  rec: "Clerk__Get" "ck" "key" :=
    let: "err" := ref (zero_val uint64T) in
    let: "opId" := ref (zero_val uint64T) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: ("0_ret", "1_ret") := Client__getFreshNumRpc (struct.loadF Clerk "rpcCl" "ck") in
      "opId" <-[uint64T] "0_ret";;
      "err" <-[uint64T] "1_ret";;
      (if: (![uint64T] "err" = #0)
      then Break
      else Continue));;
    let: "args" := struct.new getArgs [
      "opId" ::= ![uint64T] "opId";
      "key" ::= "key"
    ] in
    let: "ret" := ref (zero_val stringT) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: ("reply", "err") := Client__getRpc (struct.loadF Clerk "rpcCl" "ck") "args" in
      (if: ("err" = urpc.ErrNone)
      then
        "ret" <-[stringT] "reply";;
        Break
      else Continue));;
    ![stringT] "ret".

(* kvservice.gb.go *)

(* TODO: these are generic *)
Definition EncodeBool: val :=
  rec: "EncodeBool" "a" :=
    (if: "a"
    then SliceAppend byteT (NewSlice byteT #0) (#(U8 1))
    else SliceAppend byteT (NewSlice byteT #0) (#(U8 0))).

Definition DecodeBool: val :=
  rec: "DecodeBool" "x" :=
    (SliceGet byteT "x" #0 = #(U8 1)).

Definition EncodeUint64: val :=
  rec: "EncodeUint64" "a" :=
    marshal.WriteInt (NewSlice byteT #0) "a".

Definition decodePutArgs: val :=
  rec: "decodePutArgs" "x" :=
    let: "e" := ref_to (slice.T byteT) "x" in
    let: "a" := struct.alloc putArgs (zero_val (struct.t putArgs)) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "e") in
    struct.storeF putArgs "opId" "a" "0_ret";;
    "e" <-[slice.T byteT] "1_ret";;
    let: ("keyLen", "e") := marshal.ReadInt (![slice.T byteT] "e") in
    let: ("keyBytes", "valBytes") := marshal.ReadBytes (![slice.T byteT] "e") "keyLen" in
    struct.storeF putArgs "key" "a" (Data.bytesToString "keyBytes");;
    struct.storeF putArgs "val" "a" (Data.bytesToString "valBytes");;
    "a".

Definition decodeConditionalPutArgs: val :=
  rec: "decodeConditionalPutArgs" "x" :=
    let: "e" := ref_to (slice.T byteT) "x" in
    let: "a" := struct.alloc conditionalPutArgs (zero_val (struct.t conditionalPutArgs)) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "e") in
    struct.storeF conditionalPutArgs "opId" "a" "0_ret";;
    "e" <-[slice.T byteT] "1_ret";;
    let: ("keyLen", "e") := marshal.ReadInt (![slice.T byteT] "e") in
    let: ("keyBytes", "e") := marshal.ReadBytes (![slice.T byteT] "e") "keyLen" in
    struct.storeF conditionalPutArgs "key" "a" (Data.bytesToString "keyBytes");;
    let: ("expectedValLen", "e") := marshal.ReadInt (![slice.T byteT] "e") in
    let: ("expectedValBytes", "newValBytes") := marshal.ReadBytes (![slice.T byteT] "e") "expectedValLen" in
    struct.storeF conditionalPutArgs "expectedVal" "a" (Data.bytesToString "expectedValBytes");;
    struct.storeF conditionalPutArgs "newVal" "a" (Data.bytesToString "newValBytes");;
    "a".

Definition decodeGetArgs: val :=
  rec: "decodeGetArgs" "x" :=
    let: "e" := ref_to (slice.T byteT) "x" in
    let: "keyBytes" := ref (zero_val (slice.T byteT)) in
    let: "a" := struct.alloc getArgs (zero_val (struct.t getArgs)) in
    let: ("0_ret", "1_ret") := marshal.ReadInt (![slice.T byteT] "e") in
    struct.storeF getArgs "opId" "a" "0_ret";;
    "keyBytes" <-[slice.T byteT] "1_ret";;
    struct.storeF getArgs "key" "a" (Data.bytesToString (![slice.T byteT] "keyBytes"));;
    "a".

(* kvservice_rpc.gb.go *)

Definition Error: ty := uint64T.

(* kvservice_rpc_server.gb.go *)

(* Server from server.go *)

Definition Server := struct.decl [
  "mu" :: ptrT;
  "nextFreshId" :: uint64T;
  "lastReplies" :: mapT stringT;
  "kvs" :: mapT stringT
].

Definition Server__getFreshNum: val :=
  rec: "Server__getFreshNum" "s" :=
    lock.acquire (struct.loadF Server "mu" "s");;
    let: "n" := struct.loadF Server "nextFreshId" "s" in
    struct.storeF Server "nextFreshId" "s" (std.SumAssumeNoOverflow (struct.loadF Server "nextFreshId" "s") #1);;
    lock.release (struct.loadF Server "mu" "s");;
    "n".

Definition Server__put: val :=
  rec: "Server__put" "s" "args" :=
    lock.acquire (struct.loadF Server "mu" "s");;
    let: (<>, "ok") := MapGet (struct.loadF Server "lastReplies" "s") (struct.loadF putArgs "opId" "args") in
    (if: "ok"
    then
      lock.release (struct.loadF Server "mu" "s");;
      #()
    else
      MapInsert (struct.loadF Server "kvs" "s") (struct.loadF putArgs "key" "args") (struct.loadF putArgs "val" "args");;
      MapInsert (struct.loadF Server "lastReplies" "s") (struct.loadF putArgs "opId" "args") #(str"");;
      lock.release (struct.loadF Server "mu" "s");;
      #()).

Definition Server__conditionalPut: val :=
  rec: "Server__conditionalPut" "s" "args" :=
    lock.acquire (struct.loadF Server "mu" "s");;
    let: ("ret", "ok") := MapGet (struct.loadF Server "lastReplies" "s") (struct.loadF conditionalPutArgs "opId" "args") in
    (if: "ok"
    then
      lock.release (struct.loadF Server "mu" "s");;
      "ret"
    else
      let: "ret2" := ref_to stringT #(str"") in
      (if: (Fst (MapGet (struct.loadF Server "kvs" "s") (struct.loadF conditionalPutArgs "key" "args")) = struct.loadF conditionalPutArgs "expectedVal" "args")
      then
        MapInsert (struct.loadF Server "kvs" "s") (struct.loadF conditionalPutArgs "key" "args") (struct.loadF conditionalPutArgs "newVal" "args");;
        "ret2" <-[stringT] #(str"ok")
      else #());;
      MapInsert (struct.loadF Server "lastReplies" "s") (struct.loadF conditionalPutArgs "opId" "args") (![stringT] "ret2");;
      lock.release (struct.loadF Server "mu" "s");;
      ![stringT] "ret2").

Definition Server__get: val :=
  rec: "Server__get" "s" "args" :=
    lock.acquire (struct.loadF Server "mu" "s");;
    let: ("ret", "ok") := MapGet (struct.loadF Server "lastReplies" "s") (struct.loadF getArgs "opId" "args") in
    (if: "ok"
    then
      lock.release (struct.loadF Server "mu" "s");;
      "ret"
    else
      let: "ret2" := Fst (MapGet (struct.loadF Server "kvs" "s") (struct.loadF getArgs "key" "args")) in
      lock.release (struct.loadF Server "mu" "s");;
      "ret2").

Definition Server__Start: val :=
  rec: "Server__Start" "s" "me" :=
    let: "handlers" := NewMap ((slice.T byteT -> ptrT -> unitT)%ht) #() in
    MapInsert "handlers" rpcIdGetFreshNum ((λ: "enc_args" "enc_reply",
      "enc_reply" <-[slice.T byteT] EncodeUint64 (Server__getFreshNum "s");;
      #()
      ));;
    MapInsert "handlers" rpcIdPut ((λ: "enc_args" "enc_reply",
      Server__put "s" (decodePutArgs "enc_args");;
      #()
      ));;
    MapInsert "handlers" rpcIdConditionalPut ((λ: "enc_args" "enc_reply",
      "enc_reply" <-[slice.T byteT] Data.stringToBytes (Server__conditionalPut "s" (decodeConditionalPutArgs "enc_args"));;
      #()
      ));;
    MapInsert "handlers" rpcIdGet ((λ: "enc_args" "enc_reply",
      "enc_reply" <-[slice.T byteT] Data.stringToBytes (Server__get "s" (decodeGetArgs "enc_args"));;
      #()
      ));;
    urpc.Server__Serve (urpc.MakeServer "handlers") "me";;
    #().

(* server.go *)

Definition MakeServer: val :=
  rec: "MakeServer" <> :=
    let: "s" := struct.alloc Server (zero_val (struct.t Server)) in
    struct.storeF Server "mu" "s" (lock.new #());;
    struct.storeF Server "kvs" "s" (NewMap stringT #());;
    struct.storeF Server "lastReplies" "s" (NewMap stringT #());;
    "s".