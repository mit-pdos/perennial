(* autogenerated from github.com/goose-lang/goose/testdata/examples/append_log *)
From New.golang Require Import defn.
Require Export New.code.github_com.goose_lang.primitive.disk.
Require Export New.code.github_com.tchajed.marshal.
Require Export New.code.sync.

Definition append_log : go_string := "github.com/goose-lang/goose/testdata/examples/append_log".

From New Require Import disk_prelude.
Module append_log.
Section code.


Definition Log : go_type := structT [
  "m" :: ptrT;
  "sz" :: uint64T;
  "diskSz" :: uint64T
].

(* go: append_log.go:22:17 *)
Definition Log__mkHdr : val :=
  rec: "Log__mkHdr" "log" <> :=
    exception_do (let: "log" := (alloc "log") in
    let: "enc" := (alloc (zero_val marshal.Enc)) in
    let: "$r0" := (let: "$a0" := disk.BlockSize in
    (func_call #marshal #"NewEnc"%go) "$a0") in
    do:  ("enc" <-[#marshal.Enc] "$r0");;;
    do:  (let: "$a0" := (![#uint64T] (struct.field_ref Log "sz" (![#ptrT] "log"))) in
    (method_call #marshal #"Enc" #"PutInt" (![#marshal.Enc] "enc")) "$a0");;;
    do:  (let: "$a0" := (![#uint64T] (struct.field_ref Log "diskSz" (![#ptrT] "log"))) in
    (method_call #marshal #"Enc" #"PutInt" (![#marshal.Enc] "enc")) "$a0");;;
    return: ((method_call #marshal #"Enc" #"Finish" (![#marshal.Enc] "enc")) #())).

(* go: append_log.go:29:17 *)
Definition Log__writeHdr : val :=
  rec: "Log__writeHdr" "log" <> :=
    exception_do (let: "log" := (alloc "log") in
    do:  (let: "$a0" := #(W64 0) in
    let: "$a1" := ((method_call #append_log.append_log #"Log'ptr" #"mkHdr" (![#ptrT] "log")) #()) in
    (func_call #disk #"Write"%go) "$a0" "$a1")).

(* go: append_log.go:33:6 *)
Definition Init : val :=
  rec: "Init" "diskSz" :=
    exception_do (let: "diskSz" := (alloc "diskSz") in
    (if: (![#uint64T] "diskSz") < #(W64 1)
    then
      return: (alloc (let: "$m" := (alloc (zero_val sync.Mutex)) in
       let: "$sz" := #(W64 0) in
       let: "$diskSz" := #(W64 0) in
       struct.make Log [{
         "m" ::= "$m";
         "sz" ::= "$sz";
         "diskSz" ::= "$diskSz"
       }]), #false)
    else do:  #());;;
    let: "log" := (alloc (zero_val ptrT)) in
    let: "$r0" := (alloc (let: "$m" := (alloc (zero_val sync.Mutex)) in
    let: "$sz" := #(W64 0) in
    let: "$diskSz" := (![#uint64T] "diskSz") in
    struct.make Log [{
      "m" ::= "$m";
      "sz" ::= "$sz";
      "diskSz" ::= "$diskSz"
    }])) in
    do:  ("log" <-[#ptrT] "$r0");;;
    do:  ((method_call #append_log.append_log #"Log'ptr" #"writeHdr" (![#ptrT] "log")) #());;;
    return: (![#ptrT] "log", #true)).

(* go: append_log.go:42:6 *)
Definition Open : val :=
  rec: "Open" <> :=
    exception_do (let: "hdr" := (alloc (zero_val sliceT)) in
    let: "$r0" := (let: "$a0" := #(W64 0) in
    (func_call #disk #"Read"%go) "$a0") in
    do:  ("hdr" <-[#sliceT] "$r0");;;
    let: "dec" := (alloc (zero_val marshal.Dec)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "hdr") in
    (func_call #marshal #"NewDec"%go) "$a0") in
    do:  ("dec" <-[#marshal.Dec] "$r0");;;
    let: "sz" := (alloc (zero_val uint64T)) in
    let: "$r0" := ((method_call #marshal #"Dec" #"GetInt" (![#marshal.Dec] "dec")) #()) in
    do:  ("sz" <-[#uint64T] "$r0");;;
    let: "diskSz" := (alloc (zero_val uint64T)) in
    let: "$r0" := ((method_call #marshal #"Dec" #"GetInt" (![#marshal.Dec] "dec")) #()) in
    do:  ("diskSz" <-[#uint64T] "$r0");;;
    return: (alloc (let: "$m" := (alloc (zero_val sync.Mutex)) in
     let: "$sz" := (![#uint64T] "sz") in
     let: "$diskSz" := (![#uint64T] "diskSz") in
     struct.make Log [{
       "m" ::= "$m";
       "sz" ::= "$sz";
       "diskSz" ::= "$diskSz"
     }]))).

(* go: append_log.go:50:17 *)
Definition Log__get : val :=
  rec: "Log__get" "log" "i" :=
    exception_do (let: "log" := (alloc "log") in
    let: "i" := (alloc "i") in
    let: "sz" := (alloc (zero_val uint64T)) in
    let: "$r0" := (![#uint64T] (struct.field_ref Log "sz" (![#ptrT] "log"))) in
    do:  ("sz" <-[#uint64T] "$r0");;;
    (if: (![#uint64T] "i") < (![#uint64T] "sz")
    then
      return: (let: "$a0" := (#(W64 1) + (![#uint64T] "i")) in
       (func_call #disk #"Read"%go) "$a0", #true)
    else do:  #());;;
    return: (#slice.nil, #false)).

(* go: append_log.go:58:17 *)
Definition Log__Get : val :=
  rec: "Log__Get" "log" "i" :=
    exception_do (let: "log" := (alloc "log") in
    let: "i" := (alloc "i") in
    do:  ((method_call #sync #"Mutex'ptr" #"Lock" (![#ptrT] (struct.field_ref Log "m" (![#ptrT] "log")))) #());;;
    let: "b" := (alloc (zero_val boolT)) in
    let: "v" := (alloc (zero_val sliceT)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![#uint64T] "i") in
    (method_call #append_log.append_log #"Log'ptr" #"get" (![#ptrT] "log")) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("v" <-[#sliceT] "$r0");;;
    do:  ("b" <-[#boolT] "$r1");;;
    do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] (struct.field_ref Log "m" (![#ptrT] "log")))) #());;;
    return: (![#sliceT] "v", ![#boolT] "b")).

(* go: append_log.go:65:6 *)
Definition writeAll : val :=
  rec: "writeAll" "bks" "off" :=
    exception_do (let: "off" := (alloc "off") in
    let: "bks" := (alloc "bks") in
    let: "$range" := (![#sliceT] "bks") in
    (let: "bk" := (alloc (zero_val intT)) in
    let: "i" := (alloc (zero_val intT)) in
    slice.for_range #sliceT "$range" (λ: "$key" "$value",
      do:  ("bk" <-[#sliceT] "$value");;;
      do:  ("i" <-[#intT] "$key");;;
      do:  (let: "$a0" := ((![#uint64T] "off") + (s_to_w64 (![#intT] "i"))) in
      let: "$a1" := (![#sliceT] "bk") in
      (func_call #disk #"Write"%go) "$a0" "$a1")))).

(* go: append_log.go:71:17 *)
Definition Log__append : val :=
  rec: "Log__append" "log" "bks" :=
    exception_do (let: "log" := (alloc "log") in
    let: "bks" := (alloc "bks") in
    let: "sz" := (alloc (zero_val uint64T)) in
    let: "$r0" := (![#uint64T] (struct.field_ref Log "sz" (![#ptrT] "log"))) in
    do:  ("sz" <-[#uint64T] "$r0");;;
    (if: (s_to_w64 (let: "$a0" := (![#sliceT] "bks") in
    slice.len "$a0")) ≥ (((![#uint64T] (struct.field_ref Log "diskSz" (![#ptrT] "log"))) - #(W64 1)) - (![#uint64T] "sz"))
    then return: (#false)
    else do:  #());;;
    do:  (let: "$a0" := (![#sliceT] "bks") in
    let: "$a1" := (#(W64 1) + (![#uint64T] "sz")) in
    (func_call #append_log.append_log #"writeAll"%go) "$a0" "$a1");;;
    do:  ((struct.field_ref Log "sz" (![#ptrT] "log")) <-[#uint64T] ((![#uint64T] (struct.field_ref Log "sz" (![#ptrT] "log"))) + (s_to_w64 (let: "$a0" := (![#sliceT] "bks") in
    slice.len "$a0"))));;;
    do:  ((method_call #append_log.append_log #"Log'ptr" #"writeHdr" (![#ptrT] "log")) #());;;
    return: (#true)).

(* go: append_log.go:82:17 *)
Definition Log__Append : val :=
  rec: "Log__Append" "log" "bks" :=
    exception_do (let: "log" := (alloc "log") in
    let: "bks" := (alloc "bks") in
    do:  ((method_call #sync #"Mutex'ptr" #"Lock" (![#ptrT] (struct.field_ref Log "m" (![#ptrT] "log")))) #());;;
    let: "b" := (alloc (zero_val boolT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "bks") in
    (method_call #append_log.append_log #"Log'ptr" #"append" (![#ptrT] "log")) "$a0") in
    do:  ("b" <-[#boolT] "$r0");;;
    do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] (struct.field_ref Log "m" (![#ptrT] "log")))) #());;;
    return: (![#boolT] "b")).

(* go: append_log.go:89:17 *)
Definition Log__reset : val :=
  rec: "Log__reset" "log" <> :=
    exception_do (let: "log" := (alloc "log") in
    let: "$r0" := #(W64 0) in
    do:  ((struct.field_ref Log "sz" (![#ptrT] "log")) <-[#uint64T] "$r0");;;
    do:  ((method_call #append_log.append_log #"Log'ptr" #"writeHdr" (![#ptrT] "log")) #())).

(* go: append_log.go:94:17 *)
Definition Log__Reset : val :=
  rec: "Log__Reset" "log" <> :=
    exception_do (let: "log" := (alloc "log") in
    do:  ((method_call #sync #"Mutex'ptr" #"Lock" (![#ptrT] (struct.field_ref Log "m" (![#ptrT] "log")))) #());;;
    do:  ((method_call #append_log.append_log #"Log'ptr" #"reset" (![#ptrT] "log")) #());;;
    do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] (struct.field_ref Log "m" (![#ptrT] "log")))) #())).

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("Init"%go, Init); ("Open"%go, Open); ("writeAll"%go, writeAll)].

Definition msets' : list (go_string * (list (go_string * val))) := [("Log"%go, []); ("Log'ptr"%go, [("Append"%go, Log__Append); ("Get"%go, Log__Get); ("Reset"%go, Log__Reset); ("append"%go, Log__append); ("get"%go, Log__get); ("mkHdr"%go, Log__mkHdr); ("reset"%go, Log__reset); ("writeHdr"%go, Log__writeHdr)])].

#[global] Instance info' : PkgInfo append_log.append_log :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [sync; marshal; disk];
  |}.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init append_log.append_log (λ: <>,
      exception_do (do:  disk.initialize';;;
      do:  marshal.initialize';;;
      do:  sync.initialize')
      ).

End code.
End append_log.
