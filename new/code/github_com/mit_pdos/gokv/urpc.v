(* autogenerated from github.com/mit-pdos/gokv/urpc *)
From New.golang Require Import defn.
Require Import New.code.github_com.goose_lang.primitive.
Require Import New.code.github_com.goose_lang.std.
Require Import New.code.github_com.mit_pdos.gokv.grove_ffi.
Require Import New.code.github_com.tchajed.marshal.
Require Import New.code.log.
Require Import New.code.sync.

Definition urpc : go_string := "github.com/mit-pdos/gokv/urpc".

From New Require Import grove_prelude.
Module urpc.
Section code.


Definition Server : go_type := structT [
  "handlers" :: mapT uint64T funcT
].

(* go: urpc.go:19:20 *)
Definition Server__rpcHandle : val :=
  rec: "Server__rpcHandle" "srv" "conn" "rpcid" "seqno" "data" :=
    exception_do (let: "srv" := (mem.alloc "srv") in
    let: "data" := (mem.alloc "data") in
    let: "seqno" := (mem.alloc "seqno") in
    let: "rpcid" := (mem.alloc "rpcid") in
    let: "conn" := (mem.alloc "conn") in
    let: "replyData" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (mem.alloc (type.zero_val #sliceT)) in
    do:  ("replyData" <-[#ptrT] "$r0");;;
    let: "f" := (mem.alloc (type.zero_val #funcT)) in
    let: "$r0" := (Fst (map.get (![#(mapT uint64T funcT)] (struct.field_ref #Server #"handlers"%go (![#ptrT] "srv"))) (![#uint64T] "rpcid"))) in
    do:  ("f" <-[#funcT] "$r0");;;
    do:  (let: "$a0" := (![#sliceT] "data") in
    let: "$a1" := (![#ptrT] "replyData") in
    (![#funcT] "f") "$a0" "$a1");;;
    let: "data1" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (slice.make3 #byteT #(W64 0) (#(W64 8) + (let: "$a0" := (![#sliceT] (![#ptrT] "replyData")) in
    slice.len "$a0"))) in
    do:  ("data1" <-[#sliceT] "$r0");;;
    let: "data2" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "data1") in
    let: "$a1" := (![#uint64T] "seqno") in
    (func_call #marshal #"WriteInt"%go) "$a0" "$a1") in
    do:  ("data2" <-[#sliceT] "$r0");;;
    let: "data3" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "data2") in
    let: "$a1" := (![#sliceT] (![#ptrT] "replyData")) in
    (func_call #marshal #"WriteBytes"%go) "$a0" "$a1") in
    do:  ("data3" <-[#sliceT] "$r0");;;
    do:  (let: "$a0" := (![#grove_ffi.Connection] "conn") in
    let: "$a1" := (![#sliceT] "data3") in
    (func_call #grove_ffi #"Send"%go) "$a0" "$a1")).

(* go: urpc.go:32:6 *)
Definition MakeServer : val :=
  rec: "MakeServer" "handlers" :=
    exception_do (let: "handlers" := (mem.alloc "handlers") in
    return: (mem.alloc (let: "$handlers" := (![#(mapT uint64T funcT)] "handlers") in
     struct.make #Server [{
       "handlers" ::= "$handlers"
     }]))).

(* go: urpc.go:36:20 *)
Definition Server__readThread : val :=
  rec: "Server__readThread" "srv" "conn" :=
    exception_do (let: "srv" := (mem.alloc "srv") in
    let: "conn" := (mem.alloc "conn") in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "r" := (mem.alloc (type.zero_val #grove_ffi.ReceiveRet)) in
      let: "$r0" := (let: "$a0" := (![#grove_ffi.Connection] "conn") in
      (func_call #grove_ffi #"Receive"%go) "$a0") in
      do:  ("r" <-[#grove_ffi.ReceiveRet] "$r0");;;
      (if: ![#boolT] (struct.field_ref #grove_ffi.ReceiveRet #"Err"%go "r")
      then break: #()
      else do:  #());;;
      let: "data" := (mem.alloc (type.zero_val #sliceT)) in
      let: "$r0" := (![#sliceT] (struct.field_ref #grove_ffi.ReceiveRet #"Data"%go "r")) in
      do:  ("data" <-[#sliceT] "$r0");;;
      let: "rpcid" := (mem.alloc (type.zero_val #uint64T)) in
      let: ("$ret0", "$ret1") := (let: "$a0" := (![#sliceT] "data") in
      (func_call #marshal #"ReadInt"%go) "$a0") in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      do:  ("rpcid" <-[#uint64T] "$r0");;;
      do:  ("data" <-[#sliceT] "$r1");;;
      let: "seqno" := (mem.alloc (type.zero_val #uint64T)) in
      let: ("$ret0", "$ret1") := (let: "$a0" := (![#sliceT] "data") in
      (func_call #marshal #"ReadInt"%go) "$a0") in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      do:  ("seqno" <-[#uint64T] "$r0");;;
      do:  ("data" <-[#sliceT] "$r1");;;
      let: "req" := (mem.alloc (type.zero_val #sliceT)) in
      let: "$r0" := (![#sliceT] "data") in
      do:  ("req" <-[#sliceT] "$r0");;;
      let: "$go" := (λ: <>,
        exception_do (do:  (let: "$a0" := (![#grove_ffi.Connection] "conn") in
        let: "$a1" := (![#uint64T] "rpcid") in
        let: "$a2" := (![#uint64T] "seqno") in
        let: "$a3" := (![#sliceT] "req") in
        (method_call #urpc.urpc #"Server'ptr" #"rpcHandle" (![#ptrT] "srv")) "$a0" "$a1" "$a2" "$a3"))
        ) in
      do:  (Fork ("$go" #()));;;
      continue: #())).

(* go: urpc.go:58:20 *)
Definition Server__Serve : val :=
  rec: "Server__Serve" "srv" "host" :=
    exception_do (let: "srv" := (mem.alloc "srv") in
    let: "host" := (mem.alloc "host") in
    let: "listener" := (mem.alloc (type.zero_val #grove_ffi.Listener)) in
    let: "$r0" := (let: "$a0" := (![#uint64T] "host") in
    (func_call #grove_ffi #"Listen"%go) "$a0") in
    do:  ("listener" <-[#grove_ffi.Listener] "$r0");;;
    let: "$go" := (λ: <>,
      exception_do ((for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
        let: "conn" := (mem.alloc (type.zero_val #grove_ffi.Connection)) in
        let: "$r0" := (let: "$a0" := (![#grove_ffi.Listener] "listener") in
        (func_call #grove_ffi #"Accept"%go) "$a0") in
        do:  ("conn" <-[#grove_ffi.Connection] "$r0");;;
        let: "$go" := (λ: <>,
          exception_do (do:  (let: "$a0" := (![#grove_ffi.Connection] "conn") in
          (method_call #urpc.urpc #"Server'ptr" #"readThread" (![#ptrT] "srv")) "$a0"))
          ) in
        do:  (Fork ("$go" #()))))
      ) in
    do:  (Fork ("$go" #()))).

Definition callbackStateWaiting : expr := #(W64 0).

Definition callbackStateDone : expr := #(W64 1).

Definition callbackStateAborted : expr := #(W64 2).

Definition Callback : go_type := structT [
  "reply" :: ptrT;
  "state" :: ptrT;
  "cond" :: ptrT
].

Definition Client : go_type := structT [
  "mu" :: ptrT;
  "conn" :: grove_ffi.Connection;
  "seq" :: uint64T;
  "pending" :: mapT uint64T ptrT
].

(* go: urpc.go:88:19 *)
Definition Client__replyThread : val :=
  rec: "Client__replyThread" "cl" <> :=
    exception_do (let: "cl" := (mem.alloc "cl") in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "r" := (mem.alloc (type.zero_val #grove_ffi.ReceiveRet)) in
      let: "$r0" := (let: "$a0" := (![#grove_ffi.Connection] (struct.field_ref #Client #"conn"%go (![#ptrT] "cl"))) in
      (func_call #grove_ffi #"Receive"%go) "$a0") in
      do:  ("r" <-[#grove_ffi.ReceiveRet] "$r0");;;
      (if: ![#boolT] (struct.field_ref #grove_ffi.ReceiveRet #"Err"%go "r")
      then
        do:  ((method_call #sync #"Mutex'ptr" #"Lock" (![#ptrT] (struct.field_ref #Client #"mu"%go (![#ptrT] "cl")))) #());;;
        let: "$range" := (![#(mapT uint64T ptrT)] (struct.field_ref #Client #"pending"%go (![#ptrT] "cl"))) in
        (let: "cb" := (mem.alloc (type.zero_val #uint64T)) in
        map.for_range "$range" (λ: "$key" "value",
          do:  ("cb" <-[#ptrT] "$value");;;
          do:  "$key";;;
          let: "$r0" := callbackStateAborted in
          do:  ((![#ptrT] (struct.field_ref #Callback #"state"%go (![#ptrT] "cb"))) <-[#uint64T] "$r0");;;
          do:  ((method_call #sync #"Cond'ptr" #"Signal" (![#ptrT] (struct.field_ref #Callback #"cond"%go (![#ptrT] "cb")))) #())));;;
        do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] (struct.field_ref #Client #"mu"%go (![#ptrT] "cl")))) #());;;
        break: #()
      else do:  #());;;
      let: "data" := (mem.alloc (type.zero_val #sliceT)) in
      let: "$r0" := (![#sliceT] (struct.field_ref #grove_ffi.ReceiveRet #"Data"%go "r")) in
      do:  ("data" <-[#sliceT] "$r0");;;
      let: "seqno" := (mem.alloc (type.zero_val #uint64T)) in
      let: ("$ret0", "$ret1") := (let: "$a0" := (![#sliceT] "data") in
      (func_call #marshal #"ReadInt"%go) "$a0") in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      do:  ("seqno" <-[#uint64T] "$r0");;;
      do:  ("data" <-[#sliceT] "$r1");;;
      let: "reply" := (mem.alloc (type.zero_val #sliceT)) in
      let: "$r0" := (![#sliceT] "data") in
      do:  ("reply" <-[#sliceT] "$r0");;;
      do:  ((method_call #sync #"Mutex'ptr" #"Lock" (![#ptrT] (struct.field_ref #Client #"mu"%go (![#ptrT] "cl")))) #());;;
      let: "ok" := (mem.alloc (type.zero_val #boolT)) in
      let: "cb" := (mem.alloc (type.zero_val #ptrT)) in
      let: ("$ret0", "$ret1") := (map.get (![#(mapT uint64T ptrT)] (struct.field_ref #Client #"pending"%go (![#ptrT] "cl"))) (![#uint64T] "seqno")) in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      do:  ("cb" <-[#ptrT] "$r0");;;
      do:  ("ok" <-[#boolT] "$r1");;;
      (if: ![#boolT] "ok"
      then
        do:  (let: "$a0" := (![#(mapT uint64T ptrT)] (struct.field_ref #Client #"pending"%go (![#ptrT] "cl"))) in
        let: "$a1" := (![#uint64T] "seqno") in
        map.delete "$a0" "$a1");;;
        let: "$r0" := (![#sliceT] "reply") in
        do:  ((![#ptrT] (struct.field_ref #Callback #"reply"%go (![#ptrT] "cb"))) <-[#sliceT] "$r0");;;
        let: "$r0" := callbackStateDone in
        do:  ((![#ptrT] (struct.field_ref #Callback #"state"%go (![#ptrT] "cb"))) <-[#uint64T] "$r0");;;
        do:  ((method_call #sync #"Cond'ptr" #"Signal" (![#ptrT] (struct.field_ref #Callback #"cond"%go (![#ptrT] "cb")))) #())
      else do:  #());;;
      do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] (struct.field_ref #Client #"mu"%go (![#ptrT] "cl")))) #());;;
      continue: #())).

(* go: urpc.go:120:6 *)
Definition TryMakeClient : val :=
  rec: "TryMakeClient" "host_name" :=
    exception_do (let: "host_name" := (mem.alloc "host_name") in
    let: "host" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := (![#uint64T] "host_name") in
    do:  ("host" <-[#uint64T] "$r0");;;
    let: "a" := (mem.alloc (type.zero_val #grove_ffi.ConnectRet)) in
    let: "$r0" := (let: "$a0" := (![#uint64T] "host") in
    (func_call #grove_ffi #"Connect"%go) "$a0") in
    do:  ("a" <-[#grove_ffi.ConnectRet] "$r0");;;
    let: "nilClient" := (mem.alloc (type.zero_val #ptrT)) in
    (if: ![#boolT] (struct.field_ref #grove_ffi.ConnectRet #"Err"%go "a")
    then return: (#(W64 1), ![#ptrT] "nilClient")
    else do:  #());;;
    let: "cl" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (mem.alloc (let: "$conn" := (![#grove_ffi.Connection] (struct.field_ref #grove_ffi.ConnectRet #"Connection"%go "a")) in
    let: "$mu" := (mem.alloc (type.zero_val #sync.Mutex)) in
    let: "$seq" := #(W64 1) in
    let: "$pending" := (map.make #uint64T #ptrT) in
    struct.make #Client [{
      "mu" ::= "$mu";
      "conn" ::= "$conn";
      "seq" ::= "$seq";
      "pending" ::= "$pending"
    }])) in
    do:  ("cl" <-[#ptrT] "$r0");;;
    let: "$go" := (λ: <>,
      exception_do (do:  ((method_call #urpc.urpc #"Client'ptr" #"replyThread" (![#ptrT] "cl")) #()))
      ) in
    do:  (Fork ("$go" #()));;;
    return: (#(W64 0), ![#ptrT] "cl")).

(* go: urpc.go:140:6 *)
Definition MakeClient : val :=
  rec: "MakeClient" "host_name" :=
    exception_do (let: "host_name" := (mem.alloc "host_name") in
    let: "cl" := (mem.alloc (type.zero_val #ptrT)) in
    let: "err" := (mem.alloc (type.zero_val #uint64T)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![#uint64T] "host_name") in
    (func_call #urpc.urpc #"TryMakeClient"%go) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("err" <-[#uint64T] "$r0");;;
    do:  ("cl" <-[#ptrT] "$r1");;;
    (if: (![#uint64T] "err") ≠ #(W64 0)
    then
      do:  (let: "$a0" := #"Unable to connect to %s"%go in
      let: "$a1" := ((let: "$sl0" := (interface.make #""%go #"string"%go (let: "$a0" := (![#uint64T] "host_name") in
      (func_call #grove_ffi #"AddressToStr"%go) "$a0")) in
      slice.literal #interfaceT ["$sl0"])) in
      (func_call #log #"Printf"%go) "$a0" "$a1")
    else do:  #());;;
    do:  (let: "$a0" := ((![#uint64T] "err") = #(W64 0)) in
    (func_call #primitive #"Assume"%go) "$a0");;;
    return: (![#ptrT] "cl")).

Definition Error : go_type := uint64T.

Definition ErrNone : expr := #(W64 0).

Definition ErrTimeout : expr := #(W64 1).

Definition ErrDisconnect : expr := #(W64 2).

(* go: urpc.go:155:19 *)
Definition Client__CallStart : val :=
  rec: "Client__CallStart" "cl" "rpcid" "args" :=
    exception_do (let: "cl" := (mem.alloc "cl") in
    let: "args" := (mem.alloc "args") in
    let: "rpcid" := (mem.alloc "rpcid") in
    let: "reply_buf" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (mem.alloc (type.zero_val #sliceT)) in
    do:  ("reply_buf" <-[#ptrT] "$r0");;;
    let: "cb" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (mem.alloc (let: "$reply" := (![#ptrT] "reply_buf") in
    let: "$state" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$cond" := (let: "$a0" := (interface.make #sync #"Mutex'ptr" (![#ptrT] (struct.field_ref #Client #"mu"%go (![#ptrT] "cl")))) in
    (func_call #sync #"NewCond"%go) "$a0") in
    struct.make #Callback [{
      "reply" ::= "$reply";
      "state" ::= "$state";
      "cond" ::= "$cond"
    }])) in
    do:  ("cb" <-[#ptrT] "$r0");;;
    let: "$r0" := callbackStateWaiting in
    do:  ((![#ptrT] (struct.field_ref #Callback #"state"%go (![#ptrT] "cb"))) <-[#uint64T] "$r0");;;
    do:  ((method_call #sync #"Mutex'ptr" #"Lock" (![#ptrT] (struct.field_ref #Client #"mu"%go (![#ptrT] "cl")))) #());;;
    let: "seqno" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := (![#uint64T] (struct.field_ref #Client #"seq"%go (![#ptrT] "cl"))) in
    do:  ("seqno" <-[#uint64T] "$r0");;;
    let: "$r0" := (let: "$a0" := (![#uint64T] (struct.field_ref #Client #"seq"%go (![#ptrT] "cl"))) in
    let: "$a1" := #(W64 1) in
    (func_call #std #"SumAssumeNoOverflow"%go) "$a0" "$a1") in
    do:  ((struct.field_ref #Client #"seq"%go (![#ptrT] "cl")) <-[#uint64T] "$r0");;;
    let: "$r0" := (![#ptrT] "cb") in
    do:  (map.insert (![#(mapT uint64T ptrT)] (struct.field_ref #Client #"pending"%go (![#ptrT] "cl"))) (![#uint64T] "seqno") "$r0");;;
    do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] (struct.field_ref #Client #"mu"%go (![#ptrT] "cl")))) #());;;
    let: "data1" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (slice.make3 #byteT #(W64 0) (#(W64 (8 + 8)) + (let: "$a0" := (![#sliceT] "args") in
    slice.len "$a0"))) in
    do:  ("data1" <-[#sliceT] "$r0");;;
    let: "data2" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "data1") in
    let: "$a1" := (![#uint64T] "rpcid") in
    (func_call #marshal #"WriteInt"%go) "$a0" "$a1") in
    do:  ("data2" <-[#sliceT] "$r0");;;
    let: "data3" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "data2") in
    let: "$a1" := (![#uint64T] "seqno") in
    (func_call #marshal #"WriteInt"%go) "$a0" "$a1") in
    do:  ("data3" <-[#sliceT] "$r0");;;
    let: "reqData" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "data3") in
    let: "$a1" := (![#sliceT] "args") in
    (func_call #marshal #"WriteBytes"%go) "$a0" "$a1") in
    do:  ("reqData" <-[#sliceT] "$r0");;;
    (if: let: "$a0" := (![#grove_ffi.Connection] (struct.field_ref #Client #"conn"%go (![#ptrT] "cl"))) in
    let: "$a1" := (![#sliceT] "reqData") in
    (func_call #grove_ffi #"Send"%go) "$a0" "$a1"
    then
      return: (mem.alloc (struct.make #Callback [{
         "reply" ::= type.zero_val #ptrT;
         "state" ::= type.zero_val #ptrT;
         "cond" ::= type.zero_val #ptrT
       }]), ErrDisconnect)
    else do:  #());;;
    return: (![#ptrT] "cb", ErrNone)).

(* go: urpc.go:188:19 *)
Definition Client__CallComplete : val :=
  rec: "Client__CallComplete" "cl" "cb" "reply" "timeout_ms" :=
    exception_do (let: "cl" := (mem.alloc "cl") in
    let: "timeout_ms" := (mem.alloc "timeout_ms") in
    let: "reply" := (mem.alloc "reply") in
    let: "cb" := (mem.alloc "cb") in
    do:  ((method_call #sync #"Mutex'ptr" #"Lock" (![#ptrT] (struct.field_ref #Client #"mu"%go (![#ptrT] "cl")))) #());;;
    (if: (![#uint64T] (![#ptrT] (struct.field_ref #Callback #"state"%go (![#ptrT] "cb")))) = callbackStateWaiting
    then
      do:  (let: "$a0" := (![#ptrT] (struct.field_ref #Callback #"cond"%go (![#ptrT] "cb"))) in
      let: "$a1" := (![#uint64T] "timeout_ms") in
      (func_call #primitive #"WaitTimeout"%go) "$a0" "$a1")
    else do:  #());;;
    let: "state" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := (![#uint64T] (![#ptrT] (struct.field_ref #Callback #"state"%go (![#ptrT] "cb")))) in
    do:  ("state" <-[#uint64T] "$r0");;;
    (if: (![#uint64T] "state") = callbackStateDone
    then
      let: "$r0" := (![#sliceT] (![#ptrT] (struct.field_ref #Callback #"reply"%go (![#ptrT] "cb")))) in
      do:  ((![#ptrT] "reply") <-[#sliceT] "$r0");;;
      do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] (struct.field_ref #Client #"mu"%go (![#ptrT] "cl")))) #());;;
      return: (#(W64 0))
    else
      do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] (struct.field_ref #Client #"mu"%go (![#ptrT] "cl")))) #());;;
      (if: (![#uint64T] "state") = callbackStateAborted
      then return: (ErrDisconnect)
      else return: (ErrTimeout)))).

(* go: urpc.go:215:19 *)
Definition Client__Call : val :=
  rec: "Client__Call" "cl" "rpcid" "args" "reply" "timeout_ms" :=
    exception_do (let: "cl" := (mem.alloc "cl") in
    let: "timeout_ms" := (mem.alloc "timeout_ms") in
    let: "reply" := (mem.alloc "reply") in
    let: "args" := (mem.alloc "args") in
    let: "rpcid" := (mem.alloc "rpcid") in
    let: "err" := (mem.alloc (type.zero_val #uint64T)) in
    let: "cb" := (mem.alloc (type.zero_val #ptrT)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![#uint64T] "rpcid") in
    let: "$a1" := (![#sliceT] "args") in
    (method_call #urpc.urpc #"Client'ptr" #"CallStart" (![#ptrT] "cl")) "$a0" "$a1") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("cb" <-[#ptrT] "$r0");;;
    do:  ("err" <-[#uint64T] "$r1");;;
    (if: (![#uint64T] "err") ≠ #(W64 0)
    then return: (![#uint64T] "err")
    else do:  #());;;
    return: (let: "$a0" := (![#ptrT] "cb") in
     let: "$a1" := (![#ptrT] "reply") in
     let: "$a2" := (![#uint64T] "timeout_ms") in
     (method_call #urpc.urpc #"Client'ptr" #"CallComplete" (![#ptrT] "cl")) "$a0" "$a1" "$a2")).

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("MakeServer"%go, MakeServer); ("TryMakeClient"%go, TryMakeClient); ("MakeClient"%go, MakeClient)].

Definition msets' : list (go_string * (list (go_string * val))) := [("Server"%go, []); ("Server'ptr"%go, [("Serve"%go, Server__Serve); ("readThread"%go, Server__readThread); ("rpcHandle"%go, Server__rpcHandle)]); ("Callback"%go, []); ("Callback'ptr"%go, []); ("Client"%go, []); ("Client'ptr"%go, [("Call"%go, Client__Call); ("CallComplete"%go, Client__CallComplete); ("CallStart"%go, Client__CallStart); ("replyThread"%go, Client__replyThread)])].

#[global] Instance info' : PkgInfo urpc.urpc :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [log; sync; primitive; std; grove_ffi; marshal];
  |}.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init urpc.urpc (λ: <>,
      exception_do (do:  marshal.initialize';;;
      do:  grove_ffi.initialize';;;
      do:  std.initialize';;;
      do:  primitive.initialize';;;
      do:  sync.initialize';;;
      do:  log.initialize')
      ).

End code.
End urpc.
