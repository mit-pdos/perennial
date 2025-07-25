(* autogenerated from github.com/sanjit-bhat/pav/alicebob *)
From New.golang Require Import defn.
Require Export New.code.github_com.goose_lang.primitive.
Require Export New.code.github_com.goose_lang.std.
Require Export New.code.github_com.sanjit_bhat.pav.advrpc.
Require Export New.code.github_com.sanjit_bhat.pav.auditor.
Require Export New.code.github_com.sanjit_bhat.pav.client.
Require Export New.code.github_com.sanjit_bhat.pav.cryptoffi.
Require Export New.code.github_com.sanjit_bhat.pav.ktcore.
Require Export New.code.github_com.sanjit_bhat.pav.server.
Require Export New.code.sync.

Definition alicebob : go_string := "github.com/sanjit-bhat/pav/alicebob".

Module alicebob.
Section code.
Context `{ffi_syntax}.


Definition aliceUid : expr := #(W64 0).

Definition bobUid : expr := #(W64 1).

(* go: alicebob.go:21:6 *)
Definition testAliceBob : val :=
  rec: "testAliceBob" "servAddr" "adtrAddr" :=
    exception_do (let: "err" := (mem.alloc (type.zero_val #ktcore.Blame)) in
    let: "evid" := (mem.alloc (type.zero_val #ptrT)) in
    let: "adtrAddr" := (mem.alloc "adtrAddr") in
    let: "servAddr" := (mem.alloc "servAddr") in
    let: "servSigPk" := (mem.alloc (type.zero_val #cryptoffi.SigPublicKey)) in
    let: "serv" := (mem.alloc (type.zero_val #ptrT)) in
    let: ("$ret0", "$ret1") := ((func_call #server.server #"New"%go) #()) in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("serv" <-[#ptrT] "$r0");;;
    do:  ("servSigPk" <-[#cryptoffi.SigPublicKey] "$r1");;;
    let: "servRpc" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := (![#ptrT] "serv") in
    (func_call #server.server #"NewRpcServer"%go) "$a0") in
    do:  ("servRpc" <-[#ptrT] "$r0");;;
    do:  (let: "$a0" := (![#uint64T] "servAddr") in
    (method_call #advrpc #"Server'ptr" #"Serve" (![#ptrT] "servRpc")) "$a0");;;
    do:  (let: "$a0" := #(W64 1000000) in
    (func_call #primitive.primitive #"Sleep"%go) "$a0");;;
    let: "adtrPk" := (mem.alloc (type.zero_val #cryptoffi.SigPublicKey)) in
    let: "adtr" := (mem.alloc (type.zero_val #ptrT)) in
    let: (("$ret0", "$ret1"), "$ret2") := (let: "$a0" := (![#uint64T] "servAddr") in
    let: "$a1" := (![#cryptoffi.SigPublicKey] "servSigPk") in
    (func_call #auditor.auditor #"New"%go) "$a0" "$a1") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    let: "$r2" := "$ret2" in
    do:  ("adtr" <-[#ptrT] "$r0");;;
    do:  ("adtrPk" <-[#cryptoffi.SigPublicKey] "$r1");;;
    do:  ("err" <-[#ktcore.Blame] "$r2");;;
    (if: (![#ktcore.Blame] "err") ≠ ktcore.BlameNone
    then return: (![#ptrT] "evid", ![#ktcore.Blame] "err")
    else do:  #());;;
    let: "adtrRpc" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := (![#ptrT] "adtr") in
    (func_call #auditor.auditor #"NewRpcAuditor"%go) "$a0") in
    do:  ("adtrRpc" <-[#ptrT] "$r0");;;
    do:  (let: "$a0" := (![#uint64T] "adtrAddr") in
    (method_call #advrpc #"Server'ptr" #"Serve" (![#ptrT] "adtrRpc")) "$a0");;;
    do:  (let: "$a0" := #(W64 1000000) in
    (func_call #primitive.primitive #"Sleep"%go) "$a0");;;
    let: "alice" := (mem.alloc (type.zero_val #ptrT)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := aliceUid in
    let: "$a1" := (![#uint64T] "servAddr") in
    let: "$a2" := (![#cryptoffi.SigPublicKey] "servSigPk") in
    (func_call #client.client #"New"%go) "$a0" "$a1" "$a2") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("alice" <-[#ptrT] "$r0");;;
    do:  ("err" <-[#ktcore.Blame] "$r1");;;
    (if: (![#ktcore.Blame] "err") ≠ ktcore.BlameNone
    then return: (![#ptrT] "evid", ![#ktcore.Blame] "err")
    else do:  #());;;
    let: "bob" := (mem.alloc (type.zero_val #ptrT)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := bobUid in
    let: "$a1" := (![#uint64T] "servAddr") in
    let: "$a2" := (![#cryptoffi.SigPublicKey] "servSigPk") in
    (func_call #client.client #"New"%go) "$a0" "$a1" "$a2") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("bob" <-[#ptrT] "$r0");;;
    do:  ("err" <-[#ktcore.Blame] "$r1");;;
    (if: (![#ktcore.Blame] "err") ≠ ktcore.BlameNone
    then return: (![#ptrT] "evid", ![#ktcore.Blame] "err")
    else do:  #());;;
    let: "aliceHist" := (mem.alloc (type.zero_val #sliceT)) in
    let: "aliceErr" := (mem.alloc (type.zero_val #ktcore.Blame)) in
    let: "bobEp" := (mem.alloc (type.zero_val #uint64T)) in
    let: "bobAlicePk" := (mem.alloc (type.zero_val #ptrT)) in
    let: "bobErr" := (mem.alloc (type.zero_val #ktcore.Blame)) in
    let: "wg" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (mem.alloc (type.zero_val #sync.WaitGroup)) in
    do:  ("wg" <-[#ptrT] "$r0");;;
    do:  (let: "$a0" := #(W64 1) in
    (method_call #sync #"WaitGroup'ptr" #"Add" (![#ptrT] "wg")) "$a0");;;
    do:  (let: "$a0" := #(W64 1) in
    (method_call #sync #"WaitGroup'ptr" #"Add" (![#ptrT] "wg")) "$a0");;;
    let: "$go" := (λ: <>,
      exception_do (let: "r1" := (mem.alloc (type.zero_val #ktcore.Blame)) in
      let: "r0" := (mem.alloc (type.zero_val #sliceT)) in
      let: ("$ret0", "$ret1") := (let: "$a0" := (![#ptrT] "alice") in
      (func_call #alicebob.alicebob #"runAlice"%go) "$a0") in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      do:  ("r0" <-[#sliceT] "$r0");;;
      do:  ("r1" <-[#ktcore.Blame] "$r1");;;
      let: "$r0" := (![#sliceT] "r0") in
      do:  ("aliceHist" <-[#sliceT] "$r0");;;
      let: "$r0" := (![#ktcore.Blame] "r1") in
      do:  ("aliceErr" <-[#ktcore.Blame] "$r0");;;
      do:  ((method_call #sync #"WaitGroup'ptr" #"Done" (![#ptrT] "wg")) #());;;
      return: #())
      ) in
    do:  (Fork ("$go" #()));;;
    let: "$go" := (λ: <>,
      exception_do (let: "r2" := (mem.alloc (type.zero_val #ktcore.Blame)) in
      let: "r1" := (mem.alloc (type.zero_val #ptrT)) in
      let: "r0" := (mem.alloc (type.zero_val #uint64T)) in
      let: (("$ret0", "$ret1"), "$ret2") := (let: "$a0" := (![#ptrT] "bob") in
      (func_call #alicebob.alicebob #"runBob"%go) "$a0") in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      let: "$r2" := "$ret2" in
      do:  ("r0" <-[#uint64T] "$r0");;;
      do:  ("r1" <-[#ptrT] "$r1");;;
      do:  ("r2" <-[#ktcore.Blame] "$r2");;;
      let: "$r0" := (![#uint64T] "r0") in
      do:  ("bobEp" <-[#uint64T] "$r0");;;
      let: "$r0" := (![#ptrT] "r1") in
      do:  ("bobAlicePk" <-[#ptrT] "$r0");;;
      let: "$r0" := (![#ktcore.Blame] "r2") in
      do:  ("bobErr" <-[#ktcore.Blame] "$r0");;;
      do:  ((method_call #sync #"WaitGroup'ptr" #"Done" (![#ptrT] "wg")) #());;;
      return: #())
      ) in
    do:  (Fork ("$go" #()));;;
    do:  ((method_call #sync #"WaitGroup'ptr" #"Wait" (![#ptrT] "wg")) #());;;
    (if: (![#ktcore.Blame] "aliceErr") ≠ ktcore.BlameNone
    then
      let: "$r0" := (![#ktcore.Blame] "aliceErr") in
      do:  ("err" <-[#ktcore.Blame] "$r0");;;
      return: (![#ptrT] "evid", ![#ktcore.Blame] "err")
    else do:  #());;;
    (if: (![#ktcore.Blame] "bobErr") ≠ ktcore.BlameNone
    then
      let: "$r0" := (![#ktcore.Blame] "bobErr") in
      do:  ("err" <-[#ktcore.Blame] "$r0");;;
      return: (![#ptrT] "evid", ![#ktcore.Blame] "err")
    else do:  #());;;
    let: "adtrCli" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := (![#uint64T] "adtrAddr") in
    (func_call #advrpc.advrpc #"Dial"%go) "$a0") in
    do:  ("adtrCli" <-[#ptrT] "$r0");;;
    (let: "$r0" := (let: "$a0" := (![#ptrT] "adtrCli") in
    (func_call #auditor.auditor #"CallUpdate"%go) "$a0") in
    do:  ("err" <-[#ktcore.Blame] "$r0");;;
    (if: (![#ktcore.Blame] "err") ≠ ktcore.BlameNone
    then return: (![#ptrT] "evid", ![#ktcore.Blame] "err")
    else do:  #()));;;
    (let: ("$ret0", "$ret1") := (let: "$a0" := (![#uint64T] "adtrAddr") in
    let: "$a1" := (![#cryptoffi.SigPublicKey] "adtrPk") in
    (method_call #client #"Client'ptr" #"Audit" (![#ptrT] "alice")) "$a0" "$a1") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("evid" <-[#ptrT] "$r0");;;
    do:  ("err" <-[#ktcore.Blame] "$r1");;;
    (if: (![#ktcore.Blame] "err") ≠ ktcore.BlameNone
    then return: (![#ptrT] "evid", ![#ktcore.Blame] "err")
    else do:  #()));;;
    (let: ("$ret0", "$ret1") := (let: "$a0" := (![#uint64T] "adtrAddr") in
    let: "$a1" := (![#cryptoffi.SigPublicKey] "adtrPk") in
    (method_call #client #"Client'ptr" #"Audit" (![#ptrT] "bob")) "$a0" "$a1") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("evid" <-[#ptrT] "$r0");;;
    do:  ("err" <-[#ktcore.Blame] "$r1");;;
    (if: (![#ktcore.Blame] "err") ≠ ktcore.BlameNone
    then return: (![#ptrT] "evid", ![#ktcore.Blame] "err")
    else do:  #()));;;
    do:  (let: "$a0" := ((![#uint64T] "bobEp") < (s_to_w64 (let: "$a0" := (![#sliceT] "aliceHist") in
    slice.len "$a0"))) in
    (func_call #primitive.primitive #"Assume"%go) "$a0");;;
    let: "alicePk" := (mem.alloc (type.zero_val #ptrT)) in
    let: "$r0" := (![#ptrT] (slice.elem_ref #ptrT (![#sliceT] "aliceHist") (![#uint64T] "bobEp"))) in
    do:  ("alicePk" <-[#ptrT] "$r0");;;
    (if: (~ (let: "$a0" := (![#ptrT] "alicePk") in
    let: "$a1" := (![#ptrT] "bobAlicePk") in
    (func_call #alicebob.alicebob #"equal"%go) "$a0" "$a1"))
    then
      let: "$r0" := ktcore.BlameAdtrSig in
      do:  ("err" <-[#ktcore.Blame] "$r0");;;
      return: (![#ptrT] "evid", ![#ktcore.Blame] "err")
    else do:  #());;;
    return: (![#ptrT] "evid", ![#ktcore.Blame] "err")).

Definition histEntry : go_type := structT [
  "isReg" :: boolT;
  "pk" :: sliceT
].

(* go: alicebob.go:108:6 *)
Definition equal : val :=
  rec: "equal" "o0" "o1" :=
    exception_do (let: "o1" := (mem.alloc "o1") in
    let: "o0" := (mem.alloc "o0") in
    (if: (![#boolT] (struct.field_ref #histEntry #"isReg"%go (![#ptrT] "o0"))) ≠ (![#boolT] (struct.field_ref #histEntry #"isReg"%go (![#ptrT] "o1")))
    then return: (#false)
    else do:  #());;;
    (if: ![#boolT] (struct.field_ref #histEntry #"isReg"%go (![#ptrT] "o0"))
    then
      return: (let: "$a0" := (![#sliceT] (struct.field_ref #histEntry #"pk"%go (![#ptrT] "o0"))) in
       let: "$a1" := (![#sliceT] (struct.field_ref #histEntry #"pk"%go (![#ptrT] "o1"))) in
       (func_call #std.std #"BytesEqual"%go) "$a0" "$a1")
    else do:  #());;;
    return: (#true)).

(* runAlice does a bunch of puts.

   go: alicebob.go:119:6 *)
Definition runAlice : val :=
  rec: "runAlice" "cli" :=
    exception_do (let: "err" := (mem.alloc (type.zero_val #ktcore.Blame)) in
    let: "hist" := (mem.alloc (type.zero_val #sliceT)) in
    let: "cli" := (mem.alloc "cli") in
    let: "ep" := (mem.alloc (type.zero_val #uint64T)) in
    let: "isInsert" := (mem.alloc (type.zero_val #boolT)) in
    let: (("$ret0", "$ret1"), "$ret2") := ((method_call #client #"Client'ptr" #"SelfMon" (![#ptrT] "cli")) #()) in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    let: "$r2" := "$ret2" in
    do:  ("ep" <-[#uint64T] "$r0");;;
    do:  ("isInsert" <-[#boolT] "$r1");;;
    do:  ("err" <-[#ktcore.Blame] "$r2");;;
    (if: (![#ktcore.Blame] "err") ≠ ktcore.BlameNone
    then return: (![#sliceT] "hist", ![#ktcore.Blame] "err")
    else do:  #());;;
    do:  (let: "$a0" := (~ (![#boolT] "isInsert")) in
    (func_call #std.std #"Assert"%go) "$a0");;;
    do:  (let: "$a0" := ((![#uint64T] "ep") = #(W64 0)) in
    (func_call #primitive.primitive #"Assume"%go) "$a0");;;
    let: "$r0" := (let: "$a0" := (![#sliceT] "hist") in
    let: "$a1" := ((let: "$sl0" := (mem.alloc (struct.make #histEntry [{
      "isReg" ::= type.zero_val #boolT;
      "pk" ::= type.zero_val #sliceT
    }])) in
    slice.literal #ptrT ["$sl0"])) in
    (slice.append #ptrT) "$a0" "$a1") in
    do:  ("hist" <-[#sliceT] "$r0");;;
    (let: "i" := (mem.alloc (type.zero_val #intT)) in
    let: "$r0" := #(W64 0) in
    do:  ("i" <-[#intT] "$r0");;;
    (for: (λ: <>, int_lt (![#intT] "i") #(W64 20)); (λ: <>, do:  ("i" <-[#intT] ((![#intT] "i") + #(W64 1)))) := λ: <>,
      do:  (let: "$a0" := #(W64 5000000) in
      (func_call #primitive.primitive #"Sleep"%go) "$a0");;;
      let: "pk" := (mem.alloc (type.zero_val #sliceT)) in
      let: "$r0" := (let: "$a0" := #(W64 32) in
      (func_call #cryptoffi.cryptoffi #"RandBytes"%go) "$a0") in
      do:  ("pk" <-[#sliceT] "$r0");;;
      do:  (let: "$a0" := (![#sliceT] "pk") in
      (method_call #client #"Client'ptr" #"Put" (![#ptrT] "cli")) "$a0");;;
      (let: "$r0" := (let: "$a0" := (![#ptrT] "cli") in
      let: "$a1" := (s_to_w64 (let: "$a0" := (![#sliceT] "hist") in
      slice.len "$a0")) in
      (func_call #alicebob.alicebob #"loopPending"%go) "$a0" "$a1") in
      do:  ("err" <-[#ktcore.Blame] "$r0");;;
      (if: (![#ktcore.Blame] "err") ≠ ktcore.BlameNone
      then return: (![#sliceT] "hist", ![#ktcore.Blame] "err")
      else do:  #()));;;
      let: "$r0" := (let: "$a0" := (![#sliceT] "hist") in
      let: "$a1" := ((let: "$sl0" := (mem.alloc (let: "$isReg" := #true in
      let: "$pk" := (![#sliceT] "pk") in
      struct.make #histEntry [{
        "isReg" ::= "$isReg";
        "pk" ::= "$pk"
      }])) in
      slice.literal #ptrT ["$sl0"])) in
      (slice.append #ptrT) "$a0" "$a1") in
      do:  ("hist" <-[#sliceT] "$r0")));;;
    return: (![#sliceT] "hist", ![#ktcore.Blame] "err")).

(* go: alicebob.go:149:6 *)
Definition loopPending : val :=
  rec: "loopPending" "cli" "ep" :=
    exception_do (let: "err" := (mem.alloc (type.zero_val #ktcore.Blame)) in
    let: "ep" := (mem.alloc "ep") in
    let: "cli" := (mem.alloc "cli") in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "ep0" := (mem.alloc (type.zero_val #uint64T)) in
      let: "done" := (mem.alloc (type.zero_val #boolT)) in
      let: (("$ret0", "$ret1"), "$ret2") := ((method_call #client #"Client'ptr" #"SelfMon" (![#ptrT] "cli")) #()) in
      let: "$r0" := "$ret0" in
      let: "$r1" := "$ret1" in
      let: "$r2" := "$ret2" in
      do:  ("ep0" <-[#uint64T] "$r0");;;
      do:  ("done" <-[#boolT] "$r1");;;
      do:  ("err" <-[#ktcore.Blame] "$r2");;;
      (if: (![#ktcore.Blame] "err") ≠ ktcore.BlameNone
      then return: (![#ktcore.Blame] "err")
      else do:  #());;;
      (if: ![#boolT] "done"
      then
        do:  (let: "$a0" := ((![#uint64T] "ep0") = (![#uint64T] "ep")) in
        (func_call #primitive.primitive #"Assume"%go) "$a0");;;
        break: #()
      else do:  #()));;;
    return: (![#ktcore.Blame] "err")).

(* runBob does a get at some time in the middle of alice's puts.

   go: alicebob.go:166:6 *)
Definition runBob : val :=
  rec: "runBob" "cli" :=
    exception_do (let: "err" := (mem.alloc (type.zero_val #ktcore.Blame)) in
    let: "ent" := (mem.alloc (type.zero_val #ptrT)) in
    let: "ep" := (mem.alloc (type.zero_val #uint64T)) in
    let: "cli" := (mem.alloc "cli") in
    do:  (let: "$a0" := #(W64 120000000) in
    (func_call #primitive.primitive #"Sleep"%go) "$a0");;;
    let: "pk" := (mem.alloc (type.zero_val #sliceT)) in
    let: "isReg" := (mem.alloc (type.zero_val #boolT)) in
    let: ((("$ret0", "$ret1"), "$ret2"), "$ret3") := (let: "$a0" := aliceUid in
    (method_call #client #"Client'ptr" #"Get" (![#ptrT] "cli")) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    let: "$r2" := "$ret2" in
    let: "$r3" := "$ret3" in
    do:  ("ep" <-[#uint64T] "$r0");;;
    do:  ("isReg" <-[#boolT] "$r1");;;
    do:  ("pk" <-[#sliceT] "$r2");;;
    do:  ("err" <-[#ktcore.Blame] "$r3");;;
    let: "$r0" := (mem.alloc (let: "$isReg" := (![#boolT] "isReg") in
    let: "$pk" := (![#sliceT] "pk") in
    struct.make #histEntry [{
      "isReg" ::= "$isReg";
      "pk" ::= "$pk"
    }])) in
    do:  ("ent" <-[#ptrT] "$r0");;;
    return: (![#uint64T] "ep", ![#ptrT] "ent", ![#ktcore.Blame] "err")).

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("testAliceBob"%go, testAliceBob); ("equal"%go, equal); ("runAlice"%go, runAlice); ("loopPending"%go, loopPending); ("runBob"%go, runBob)].

Definition msets' : list (go_string * (list (go_string * val))) := [("histEntry"%go, []); ("histEntry'ptr"%go, [])].

#[global] Instance info' : PkgInfo alicebob.alicebob :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [sync.sync; primitive.primitive; std.std; advrpc.advrpc; auditor.auditor; client.client; cryptoffi.cryptoffi; ktcore.ktcore; server.server];
  |}.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init alicebob.alicebob (λ: <>,
      exception_do (do:  server.initialize';;;
      do:  ktcore.initialize';;;
      do:  cryptoffi.initialize';;;
      do:  client.initialize';;;
      do:  auditor.initialize';;;
      do:  advrpc.initialize';;;
      do:  std.initialize';;;
      do:  primitive.initialize';;;
      do:  sync.initialize')
      ).

End code.
End alicebob.
