(* autogenerated from github.com/mit-pdos/gokv/bank *)
From New.golang Require Import defn.
From New.code Require github_com.goose_lang.primitive.
From New.code Require github_com.mit_pdos.gokv.kv.
From New.code Require github_com.mit_pdos.gokv.lockservice.
From New.code Require github_com.tchajed.marshal.

Section code.
Context `{ffi_syntax}.

Definition BAL_TOTAL : expr := #(W64 1000).

Definition BankClerk : go_type := structT [
  "lck" :: ptrT;
  "kvck" :: kv.Kv;
  "accts" :: sliceT
].

(* go: bank.go:19:6 *)
Definition acquire_two_good : val :=
  rec: "acquire_two_good" "lck" "l1" "l2" :=
    exception_do (let: "l2" := (ref_ty stringT "l2") in
    let: "l1" := (ref_ty stringT "l1") in
    let: "lck" := (ref_ty ptrT "lck") in
    (if: (![stringT] "l1") < (![stringT] "l2")
    then
      do:  (let: "$a0" := (![stringT] "l1") in
      (method_call #lockservice.pkg_name' #"LockClerk'ptr" #"Lock" #() (![ptrT] "lck")) "$a0");;;
      do:  (let: "$a0" := (![stringT] "l2") in
      (method_call #lockservice.pkg_name' #"LockClerk'ptr" #"Lock" #() (![ptrT] "lck")) "$a0")
    else
      do:  (let: "$a0" := (![stringT] "l2") in
      (method_call #lockservice.pkg_name' #"LockClerk'ptr" #"Lock" #() (![ptrT] "lck")) "$a0");;;
      do:  (let: "$a0" := (![stringT] "l1") in
      (method_call #lockservice.pkg_name' #"LockClerk'ptr" #"Lock" #() (![ptrT] "lck")) "$a0"));;;
    return: (#())).

(* go: bank.go:30:6 *)
Definition acquire_two : val :=
  rec: "acquire_two" "lck" "l1" "l2" :=
    exception_do (let: "l2" := (ref_ty stringT "l2") in
    let: "l1" := (ref_ty stringT "l1") in
    let: "lck" := (ref_ty ptrT "lck") in
    do:  (let: "$a0" := (![stringT] "l1") in
    (method_call #lockservice.pkg_name' #"LockClerk'ptr" #"Lock" #() (![ptrT] "lck")) "$a0");;;
    do:  (let: "$a0" := (![stringT] "l2") in
    (method_call #lockservice.pkg_name' #"LockClerk'ptr" #"Lock" #() (![ptrT] "lck")) "$a0");;;
    return: (#())).

(* go: bank.go:37:6 *)
Definition release_two : val :=
  rec: "release_two" "lck" "l1" "l2" :=
    exception_do (let: "l2" := (ref_ty stringT "l2") in
    let: "l1" := (ref_ty stringT "l1") in
    let: "lck" := (ref_ty ptrT "lck") in
    do:  (let: "$a0" := (![stringT] "l1") in
    (method_call #lockservice.pkg_name' #"LockClerk'ptr" #"Unlock" #() (![ptrT] "lck")) "$a0");;;
    do:  (let: "$a0" := (![stringT] "l2") in
    (method_call #lockservice.pkg_name' #"LockClerk'ptr" #"Unlock" #() (![ptrT] "lck")) "$a0");;;
    return: (#())).

(* go: bank.go:43:6 *)
Definition encodeInt : val :=
  rec: "encodeInt" "a" :=
    exception_do (let: "a" := (ref_ty uint64T "a") in
    return: (string.from_bytes (let: "$a0" := #slice.nil in
     let: "$a1" := (![uint64T] "a") in
     (func_call #marshal.pkg_name' #"WriteInt"%go) "$a0" "$a1"))).

(* go: bank.go:47:6 *)
Definition decodeInt : val :=
  rec: "decodeInt" "a" :=
    exception_do (let: "a" := (ref_ty stringT "a") in
    let: "v" := (ref_ty uint64T (zero_val uint64T)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (string.to_bytes (![stringT] "a")) in
    (func_call #marshal.pkg_name' #"ReadInt"%go) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("v" <-[uint64T] "$r0");;;
    do:  "$r1";;;
    return: (![uint64T] "v")).

Definition pkg_name' : go_string := "github.com/mit-pdos/gokv/bank".

(* Requires that the account numbers are smaller than num_accounts
   If account balance in acc_from is at least amount, transfer amount to acc_to

   go: bank.go:54:23 *)
Definition BankClerk__transfer_internal : val :=
  rec: "BankClerk__transfer_internal" "bck" "acc_from" "acc_to" "amount" :=
    exception_do (let: "bck" := (ref_ty ptrT "bck") in
    let: "amount" := (ref_ty uint64T "amount") in
    let: "acc_to" := (ref_ty stringT "acc_to") in
    let: "acc_from" := (ref_ty stringT "acc_from") in
    do:  (let: "$a0" := (![ptrT] (struct.field_ref BankClerk "lck" (![ptrT] "bck"))) in
    let: "$a1" := (![stringT] "acc_from") in
    let: "$a2" := (![stringT] "acc_to") in
    (func_call #pkg_name' #"acquire_two"%go) "$a0" "$a1" "$a2");;;
    let: "old_amount" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (let: "$a0" := (let: "$a0" := (![stringT] "acc_from") in
    (interface.get "Get" (![kv.Kv] (struct.field_ref BankClerk "kvck" (![ptrT] "bck")))) "$a0") in
    (func_call #pkg_name' #"decodeInt"%go) "$a0") in
    do:  ("old_amount" <-[uint64T] "$r0");;;
    (if: (![uint64T] "old_amount") ≥ (![uint64T] "amount")
    then
      do:  (let: "$a0" := (![stringT] "acc_from") in
      let: "$a1" := (let: "$a0" := ((![uint64T] "old_amount") - (![uint64T] "amount")) in
      (func_call #pkg_name' #"encodeInt"%go) "$a0") in
      (interface.get "Put" (![kv.Kv] (struct.field_ref BankClerk "kvck" (![ptrT] "bck")))) "$a0" "$a1");;;
      do:  (let: "$a0" := (![stringT] "acc_to") in
      let: "$a1" := (let: "$a0" := ((let: "$a0" := (let: "$a0" := (![stringT] "acc_to") in
      (interface.get "Get" (![kv.Kv] (struct.field_ref BankClerk "kvck" (![ptrT] "bck")))) "$a0") in
      (func_call #pkg_name' #"decodeInt"%go) "$a0") + (![uint64T] "amount")) in
      (func_call #pkg_name' #"encodeInt"%go) "$a0") in
      (interface.get "Put" (![kv.Kv] (struct.field_ref BankClerk "kvck" (![ptrT] "bck")))) "$a0" "$a1")
    else do:  #());;;
    do:  (let: "$a0" := (![ptrT] (struct.field_ref BankClerk "lck" (![ptrT] "bck"))) in
    let: "$a1" := (![stringT] "acc_from") in
    let: "$a2" := (![stringT] "acc_to") in
    (func_call #pkg_name' #"release_two"%go) "$a0" "$a1" "$a2")).

(* go: bank.go:65:23 *)
Definition BankClerk__SimpleTransfer : val :=
  rec: "BankClerk__SimpleTransfer" "bck" <> :=
    exception_do (let: "bck" := (ref_ty ptrT "bck") in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "src" := (ref_ty uint64T (zero_val uint64T)) in
      let: "$r0" := ((func_call #primitive.pkg_name' #"RandomUint64"%go) #()) in
      do:  ("src" <-[uint64T] "$r0");;;
      let: "dst" := (ref_ty uint64T (zero_val uint64T)) in
      let: "$r0" := ((func_call #primitive.pkg_name' #"RandomUint64"%go) #()) in
      do:  ("dst" <-[uint64T] "$r0");;;
      let: "amount" := (ref_ty uint64T (zero_val uint64T)) in
      let: "$r0" := ((func_call #primitive.pkg_name' #"RandomUint64"%go) #()) in
      do:  ("amount" <-[uint64T] "$r0");;;
      (if: (((![uint64T] "src") < (let: "$a0" := (![sliceT] (struct.field_ref BankClerk "accts" (![ptrT] "bck"))) in
      slice.len "$a0")) && ((![uint64T] "dst") < (let: "$a0" := (![sliceT] (struct.field_ref BankClerk "accts" (![ptrT] "bck"))) in
      slice.len "$a0"))) && ((![uint64T] "src") ≠ (![uint64T] "dst"))
      then
        do:  (let: "$a0" := (![stringT] (slice.elem_ref stringT (![sliceT] (struct.field_ref BankClerk "accts" (![ptrT] "bck"))) (![uint64T] "src"))) in
        let: "$a1" := (![stringT] (slice.elem_ref stringT (![sliceT] (struct.field_ref BankClerk "accts" (![ptrT] "bck"))) (![uint64T] "dst"))) in
        let: "$a2" := (![uint64T] "amount") in
        (method_call #pkg_name' #"BankClerk'ptr" #"transfer_internal" #() (![ptrT] "bck")) "$a0" "$a1" "$a2")
      else do:  #()))).

(* go: bank.go:76:23 *)
Definition BankClerk__get_total : val :=
  rec: "BankClerk__get_total" "bck" <> :=
    exception_do (let: "bck" := (ref_ty ptrT "bck") in
    let: "sum" := (ref_ty uint64T (zero_val uint64T)) in
    do:  (let: "$range" := (![sliceT] (struct.field_ref BankClerk "accts" (![ptrT] "bck"))) in
    slice.for_range stringT "$range" (λ: <> "acct",
      let: "acct" := ref_ty stringT "acct" in
      do:  (let: "$a0" := (![stringT] "acct") in
      (method_call #lockservice.pkg_name' #"LockClerk'ptr" #"Lock" #() (![ptrT] (struct.field_ref BankClerk "lck" (![ptrT] "bck")))) "$a0");;;
      let: "$r0" := ((![uint64T] "sum") + (let: "$a0" := (let: "$a0" := (![stringT] "acct") in
      (interface.get "Get" (![kv.Kv] (struct.field_ref BankClerk "kvck" (![ptrT] "bck")))) "$a0") in
      (func_call #pkg_name' #"decodeInt"%go) "$a0")) in
      do:  ("sum" <-[uint64T] "$r0")));;;
    do:  (let: "$range" := (![sliceT] (struct.field_ref BankClerk "accts" (![ptrT] "bck"))) in
    slice.for_range stringT "$range" (λ: <> "acct",
      let: "acct" := ref_ty stringT "acct" in
      do:  (let: "$a0" := (![stringT] "acct") in
      (method_call #lockservice.pkg_name' #"LockClerk'ptr" #"Unlock" #() (![ptrT] (struct.field_ref BankClerk "lck" (![ptrT] "bck")))) "$a0")));;;
    return: (![uint64T] "sum")).

(* go: bank.go:92:23 *)
Definition BankClerk__SimpleAudit : val :=
  rec: "BankClerk__SimpleAudit" "bck" <> :=
    exception_do (let: "bck" := (ref_ty ptrT "bck") in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: ((method_call #pkg_name' #"BankClerk'ptr" #"get_total" #() (![ptrT] "bck")) #()) ≠ BAL_TOTAL
      then
        do:  (let: "$a0" := (interface.make #""%go #"string"%go #"Balance total invariant violated"%go) in
        Panic "$a0")
      else do:  #()))).

(* go: bank.go:100:6 *)
Definition MakeBankClerkSlice : val :=
  rec: "MakeBankClerkSlice" "lck" "kv" "init_flag" "accts" :=
    exception_do (let: "accts" := (ref_ty sliceT "accts") in
    let: "init_flag" := (ref_ty stringT "init_flag") in
    let: "kv" := (ref_ty kv.Kv "kv") in
    let: "lck" := (ref_ty ptrT "lck") in
    let: "bck" := (ref_ty ptrT (zero_val ptrT)) in
    let: "$r0" := (ref_ty BankClerk (zero_val BankClerk)) in
    do:  ("bck" <-[ptrT] "$r0");;;
    let: "$r0" := (![ptrT] "lck") in
    do:  ((struct.field_ref BankClerk "lck" (![ptrT] "bck")) <-[ptrT] "$r0");;;
    let: "$r0" := (![kv.Kv] "kv") in
    do:  ((struct.field_ref BankClerk "kvck" (![ptrT] "bck")) <-[kv.Kv] "$r0");;;
    let: "$r0" := (![sliceT] "accts") in
    do:  ((struct.field_ref BankClerk "accts" (![ptrT] "bck")) <-[sliceT] "$r0");;;
    do:  (let: "$a0" := (![stringT] "init_flag") in
    (method_call #lockservice.pkg_name' #"LockClerk'ptr" #"Lock" #() (![ptrT] (struct.field_ref BankClerk "lck" (![ptrT] "bck")))) "$a0");;;
    (if: (let: "$a0" := (![stringT] "init_flag") in
    (interface.get "Get" (![kv.Kv] (struct.field_ref BankClerk "kvck" (![ptrT] "bck")))) "$a0") = #""%go
    then
      do:  (let: "$a0" := (![stringT] (slice.elem_ref stringT (![sliceT] (struct.field_ref BankClerk "accts" (![ptrT] "bck"))) #(W64 0))) in
      let: "$a1" := (let: "$a0" := BAL_TOTAL in
      (func_call #pkg_name' #"encodeInt"%go) "$a0") in
      (interface.get "Put" (![kv.Kv] (struct.field_ref BankClerk "kvck" (![ptrT] "bck")))) "$a0" "$a1");;;
      do:  (let: "$range" := (let: "$s" := (![sliceT] (struct.field_ref BankClerk "accts" (![ptrT] "bck"))) in
      slice.slice stringT "$s" #(W64 1) (slice.len "$s")) in
      slice.for_range stringT "$range" (λ: <> "acct",
        let: "acct" := ref_ty stringT "acct" in
        do:  (let: "$a0" := (![stringT] "acct") in
        let: "$a1" := (let: "$a0" := #(W64 0) in
        (func_call #pkg_name' #"encodeInt"%go) "$a0") in
        (interface.get "Put" (![kv.Kv] (struct.field_ref BankClerk "kvck" (![ptrT] "bck")))) "$a0" "$a1")));;;
      do:  (let: "$a0" := (![stringT] "init_flag") in
      let: "$a1" := #"1"%go in
      (interface.get "Put" (![kv.Kv] (struct.field_ref BankClerk "kvck" (![ptrT] "bck")))) "$a0" "$a1")
    else do:  #());;;
    do:  (let: "$a0" := (![stringT] "init_flag") in
    (method_call #lockservice.pkg_name' #"LockClerk'ptr" #"Unlock" #() (![ptrT] (struct.field_ref BankClerk "lck" (![ptrT] "bck")))) "$a0");;;
    return: (![ptrT] "bck")).

(* go: bank.go:120:6 *)
Definition MakeBankClerk : val :=
  rec: "MakeBankClerk" "lck" "kv" "init_flag" "acc1" "acc2" :=
    exception_do (let: "acc2" := (ref_ty stringT "acc2") in
    let: "acc1" := (ref_ty stringT "acc1") in
    let: "init_flag" := (ref_ty stringT "init_flag") in
    let: "kv" := (ref_ty kv.Kv "kv") in
    let: "lck" := (ref_ty ptrT "lck") in
    let: "accts" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "accts") in
    let: "$a1" := ((let: "$sl0" := (![stringT] "acc1") in
    slice.literal stringT ["$sl0"])) in
    (slice.append sliceT) "$a0" "$a1") in
    do:  ("accts" <-[sliceT] "$r0");;;
    let: "$r0" := (let: "$a0" := (![sliceT] "accts") in
    let: "$a1" := ((let: "$sl0" := (![stringT] "acc2") in
    slice.literal stringT ["$sl0"])) in
    (slice.append sliceT) "$a0" "$a1") in
    do:  ("accts" <-[sliceT] "$r0");;;
    return: (let: "$a0" := (![ptrT] "lck") in
     let: "$a1" := (![kv.Kv] "kv") in
     let: "$a2" := (![stringT] "init_flag") in
     let: "$a3" := (![sliceT] "accts") in
     (func_call #pkg_name' #"MakeBankClerkSlice"%go) "$a0" "$a1" "$a2" "$a3")).

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("acquire_two_good"%go, acquire_two_good); ("acquire_two"%go, acquire_two); ("release_two"%go, release_two); ("encodeInt"%go, encodeInt); ("decodeInt"%go, decodeInt); ("MakeBankClerkSlice"%go, MakeBankClerkSlice); ("MakeBankClerk"%go, MakeBankClerk)].

Definition msets' : list (go_string * (list (go_string * val))) := [("BankClerk"%go, []); ("BankClerk'ptr"%go, [("SimpleAudit"%go, BankClerk__SimpleAudit); ("SimpleTransfer"%go, BankClerk__SimpleTransfer); ("get_total"%go, BankClerk__get_total); ("transfer_internal"%go, BankClerk__transfer_internal)])].

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' vars' functions' msets' (λ: <>,
      exception_do (do:  marshal.initialize';;;
      do:  lockservice.initialize';;;
      do:  kv.initialize';;;
      do:  primitive.initialize')
      ).

End code.
