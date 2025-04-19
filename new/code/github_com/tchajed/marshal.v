(* autogenerated from github.com/tchajed/marshal *)
From New.golang Require Import defn.
Require Import New.code.github_com.goose_lang.primitive.
Require Import New.code.github_com.goose_lang.std.

Definition marshal : go_string := "github.com/tchajed/marshal".

Module marshal.
Section code.
Context `{ffi_syntax}.


(* go: stateless.go:8:6 *)
Definition compute_new_cap : val :=
  rec: "compute_new_cap" "old_cap" "min_cap" :=
    exception_do (let: "min_cap" := (mem.alloc "min_cap") in
    let: "old_cap" := (mem.alloc "old_cap") in
    let: "new_cap" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := ((![#uint64T] "old_cap") * #(W64 2)) in
    do:  ("new_cap" <-[#uint64T] "$r0");;;
    (if: (![#uint64T] "new_cap") < (![#uint64T] "min_cap")
    then
      let: "$r0" := (![#uint64T] "min_cap") in
      do:  ("new_cap" <-[#uint64T] "$r0")
    else do:  #());;;
    return: (![#uint64T] "new_cap")).

(* Grow a slice to have at least `additional` unused bytes in the capacity.
   Runtime-check against overflow.

   go: stateless.go:19:6 *)
Definition reserve : val :=
  rec: "reserve" "b" "additional" :=
    exception_do (let: "additional" := (mem.alloc "additional") in
    let: "b" := (mem.alloc "b") in
    let: "min_cap" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := (let: "$a0" := (s_to_w64 (let: "$a0" := (![#sliceT] "b") in
    slice.len "$a0")) in
    let: "$a1" := (![#uint64T] "additional") in
    (func_call #std #"SumAssumeNoOverflow"%go) "$a0" "$a1") in
    do:  ("min_cap" <-[#uint64T] "$r0");;;
    (if: (s_to_w64 (let: "$a0" := (![#sliceT] "b") in
    slice.cap "$a0")) < (![#uint64T] "min_cap")
    then
      let: "new_cap" := (mem.alloc (type.zero_val #uint64T)) in
      let: "$r0" := (let: "$a0" := (s_to_w64 (let: "$a0" := (![#sliceT] "b") in
      slice.cap "$a0")) in
      let: "$a1" := (![#uint64T] "min_cap") in
      (func_call #marshal.marshal #"compute_new_cap"%go) "$a0" "$a1") in
      do:  ("new_cap" <-[#uint64T] "$r0");;;
      let: "dest" := (mem.alloc (type.zero_val #sliceT)) in
      let: "$r0" := (slice.make3 #byteT (let: "$a0" := (![#sliceT] "b") in
      slice.len "$a0") (![#uint64T] "new_cap")) in
      do:  ("dest" <-[#sliceT] "$r0");;;
      do:  (let: "$a0" := (![#sliceT] "dest") in
      let: "$a1" := (![#sliceT] "b") in
      (slice.copy #byteT) "$a0" "$a1");;;
      return: (![#sliceT] "dest")
    else return: (![#sliceT] "b"))).

(* go: stateless.go:40:6 *)
Definition ReadInt : val :=
  rec: "ReadInt" "b" :=
    exception_do (let: "b" := (mem.alloc "b") in
    let: "i" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "b") in
    (func_call #primitive #"UInt64Get"%go) "$a0") in
    do:  ("i" <-[#uint64T] "$r0");;;
    return: (![#uint64T] "i", let: "$s" := (![#sliceT] "b") in
     slice.slice #byteT "$s" #(W64 8) (slice.len "$s"))).

(* go: stateless.go:45:6 *)
Definition ReadInt32 : val :=
  rec: "ReadInt32" "b" :=
    exception_do (let: "b" := (mem.alloc "b") in
    let: "i" := (mem.alloc (type.zero_val #uint32T)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "b") in
    (func_call #primitive #"UInt32Get"%go) "$a0") in
    do:  ("i" <-[#uint32T] "$r0");;;
    return: (![#uint32T] "i", let: "$s" := (![#sliceT] "b") in
     slice.slice #byteT "$s" #(W64 4) (slice.len "$s"))).

(* ReadBytes reads `l` bytes from b and returns (bs, rest)

   go: stateless.go:51:6 *)
Definition ReadBytes : val :=
  rec: "ReadBytes" "b" "l" :=
    exception_do (let: "l" := (mem.alloc "l") in
    let: "b" := (mem.alloc "b") in
    let: "s" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (let: "$s" := (![#sliceT] "b") in
    slice.slice #byteT "$s" #(W64 0) (![#uint64T] "l")) in
    do:  ("s" <-[#sliceT] "$r0");;;
    return: (![#sliceT] "s", let: "$s" := (![#sliceT] "b") in
     slice.slice #byteT "$s" (![#uint64T] "l") (slice.len "$s"))).

(* Like ReadBytes, but avoids keeping the source slice [b] alive.

   go: stateless.go:57:6 *)
Definition ReadBytesCopy : val :=
  rec: "ReadBytesCopy" "b" "l" :=
    exception_do (let: "l" := (mem.alloc "l") in
    let: "b" := (mem.alloc "b") in
    let: "s" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (slice.make2 #byteT (![#uint64T] "l")) in
    do:  ("s" <-[#sliceT] "$r0");;;
    do:  (let: "$a0" := (![#sliceT] "s") in
    let: "$a1" := (let: "$s" := (![#sliceT] "b") in
    slice.slice #byteT "$s" #(W64 0) (![#uint64T] "l")) in
    (slice.copy #byteT) "$a0" "$a1");;;
    return: (![#sliceT] "s", let: "$s" := (![#sliceT] "b") in
     slice.slice #byteT "$s" (![#uint64T] "l") (slice.len "$s"))).

(* go: stateless.go:63:6 *)
Definition ReadBool : val :=
  rec: "ReadBool" "b" :=
    exception_do (let: "b" := (mem.alloc "b") in
    let: "x" := (mem.alloc (type.zero_val #boolT)) in
    let: "$r0" := ((![#byteT] (slice.elem_ref #byteT (![#sliceT] "b") #(W64 0))) ≠ #(W8 0)) in
    do:  ("x" <-[#boolT] "$r0");;;
    return: (![#boolT] "x", let: "$s" := (![#sliceT] "b") in
     slice.slice #byteT "$s" #(W64 1) (slice.len "$s"))).

(* WriteInt appends i in little-endian format to b, returning the new slice.

   go: stateless.go:77:6 *)
Definition WriteInt : val :=
  rec: "WriteInt" "b" "i" :=
    exception_do (let: "i" := (mem.alloc "i") in
    let: "b" := (mem.alloc "b") in
    let: "b2" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "b") in
    let: "$a1" := #(W64 8) in
    (func_call #marshal.marshal #"reserve"%go) "$a0" "$a1") in
    do:  ("b2" <-[#sliceT] "$r0");;;
    let: "off" := (mem.alloc (type.zero_val #intT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "b2") in
    slice.len "$a0") in
    do:  ("off" <-[#intT] "$r0");;;
    let: "b3" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (let: "$s" := (![#sliceT] "b2") in
    slice.slice #byteT "$s" #(W64 0) ((![#intT] "off") + #(W64 8))) in
    do:  ("b3" <-[#sliceT] "$r0");;;
    do:  (let: "$a0" := (let: "$s" := (![#sliceT] "b3") in
    slice.slice #byteT "$s" (![#intT] "off") (slice.len "$s")) in
    let: "$a1" := (![#uint64T] "i") in
    (func_call #primitive #"UInt64Put"%go) "$a0" "$a1");;;
    return: (![#sliceT] "b3")).

(* WriteInt32 appends 32-bit integer i in little-endian format to b, returning the new slice.

   go: stateless.go:87:6 *)
Definition WriteInt32 : val :=
  rec: "WriteInt32" "b" "i" :=
    exception_do (let: "i" := (mem.alloc "i") in
    let: "b" := (mem.alloc "b") in
    let: "b2" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "b") in
    let: "$a1" := #(W64 4) in
    (func_call #marshal.marshal #"reserve"%go) "$a0" "$a1") in
    do:  ("b2" <-[#sliceT] "$r0");;;
    let: "off" := (mem.alloc (type.zero_val #intT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "b2") in
    slice.len "$a0") in
    do:  ("off" <-[#intT] "$r0");;;
    let: "b3" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (let: "$s" := (![#sliceT] "b2") in
    slice.slice #byteT "$s" #(W64 0) ((![#intT] "off") + #(W64 4))) in
    do:  ("b3" <-[#sliceT] "$r0");;;
    do:  (let: "$a0" := (let: "$s" := (![#sliceT] "b3") in
    slice.slice #byteT "$s" (![#intT] "off") (slice.len "$s")) in
    let: "$a1" := (![#uint32T] "i") in
    (func_call #primitive #"UInt32Put"%go) "$a0" "$a1");;;
    return: (![#sliceT] "b3")).

(* Append data to b, returning the new slice.

   go: stateless.go:96:6 *)
Definition WriteBytes : val :=
  rec: "WriteBytes" "b" "data" :=
    exception_do (let: "data" := (mem.alloc "data") in
    let: "b" := (mem.alloc "b") in
    return: (let: "$a0" := (![#sliceT] "b") in
     let: "$a1" := (![#sliceT] "data") in
     (slice.append #byteT) "$a0" "$a1")).

(* go: stateless.go:100:6 *)
Definition WriteBool : val :=
  rec: "WriteBool" "b" "x" :=
    exception_do (let: "x" := (mem.alloc "x") in
    let: "b" := (mem.alloc "b") in
    (if: ![#boolT] "x"
    then
      return: (let: "$a0" := (![#sliceT] "b") in
       let: "$a1" := ((let: "$sl0" := #(W8 1) in
       slice.literal #byteT ["$sl0"])) in
       (slice.append #byteT) "$a0" "$a1")
    else
      return: (let: "$a0" := (![#sliceT] "b") in
       let: "$a1" := ((let: "$sl0" := #(W8 0) in
       slice.literal #byteT ["$sl0"])) in
       (slice.append #byteT) "$a0" "$a1"))).

(* go: stateless.go:108:6 *)
Definition WriteLenPrefixedBytes : val :=
  rec: "WriteLenPrefixedBytes" "b" "bs" :=
    exception_do (let: "bs" := (mem.alloc "bs") in
    let: "b" := (mem.alloc "b") in
    let: "b2" := (mem.alloc (type.zero_val #sliceT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "b") in
    let: "$a1" := (s_to_w64 (let: "$a0" := (![#sliceT] "bs") in
    slice.len "$a0")) in
    (func_call #marshal.marshal #"WriteInt"%go) "$a0" "$a1") in
    do:  ("b2" <-[#sliceT] "$r0");;;
    return: (let: "$a0" := (![#sliceT] "b2") in
     let: "$a1" := (![#sliceT] "bs") in
     (func_call #marshal.marshal #"WriteBytes"%go) "$a0" "$a1")).

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("compute_new_cap"%go, compute_new_cap); ("reserve"%go, reserve); ("ReadInt"%go, ReadInt); ("ReadInt32"%go, ReadInt32); ("ReadBytes"%go, ReadBytes); ("ReadBytesCopy"%go, ReadBytesCopy); ("ReadBool"%go, ReadBool); ("WriteInt"%go, WriteInt); ("WriteInt32"%go, WriteInt32); ("WriteBytes"%go, WriteBytes); ("WriteBool"%go, WriteBool); ("WriteLenPrefixedBytes"%go, WriteLenPrefixedBytes)].

Definition msets' : list (go_string * (list (go_string * val))) := [].

#[global] Instance info' : PkgInfo marshal.marshal :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [primitive; std];
  |}.

Axiom _'init : val.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init marshal.marshal (λ: <>,
      exception_do (do:  std.initialize';;;
      do:  primitive.initialize')
      ).

End code.
End marshal.
