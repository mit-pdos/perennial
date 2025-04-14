(* autogenerated from github.com/goose-lang/std *)
From New.golang Require Import defn.
Require Export New.code.github_com.goose_lang.primitive.
Require Export New.code.sync.

Definition std : go_string := "github.com/goose-lang/std".

Module std.
Section code.
Context `{ffi_syntax}.


(* Assert(b) panics if b doesn't hold

   go: goose_std.go:10:6 *)
Definition Assert : val :=
  rec: "Assert" "b" :=
    exception_do (let: "b" := (alloc "b") in
    (if: (~ (![#boolT] "b"))
    then
      do:  (let: "$a0" := (interface.make #""%go #"string"%go #"assertion failure"%go) in
      Panic "$a0")
    else do:  #())).

(* BytesEqual returns if the two byte slices are equal.

   go: goose_std.go:17:6 *)
Definition BytesEqual : val :=
  rec: "BytesEqual" "x" "y" :=
    exception_do (let: "y" := (alloc "y") in
    let: "x" := (alloc "x") in
    let: "xlen" := (alloc (type.zero_val #intT)) in
    let: "$r0" := (let: "$a0" := (![#sliceT] "x") in
    slice.len "$a0") in
    do:  ("xlen" <-[#intT] "$r0");;;
    (if: (![#intT] "xlen") ≠ (let: "$a0" := (![#sliceT] "y") in
    slice.len "$a0")
    then return: (#false)
    else do:  #());;;
    let: "i" := (alloc (type.zero_val #uint64T)) in
    let: "$r0" := #(W64 0) in
    do:  ("i" <-[#uint64T] "$r0");;;
    let: "retval" := (alloc (type.zero_val #boolT)) in
    let: "$r0" := #true in
    do:  ("retval" <-[#boolT] "$r0");;;
    (for: (λ: <>, (![#uint64T] "i") < (s_to_w64 (![#intT] "xlen"))); (λ: <>, Skip) := λ: <>,
      (if: (![#byteT] (slice.elem_ref #byteT (![#sliceT] "x") (![#uint64T] "i"))) ≠ (![#byteT] (slice.elem_ref #byteT (![#sliceT] "y") (![#uint64T] "i")))
      then
        let: "$r0" := #false in
        do:  ("retval" <-[#boolT] "$r0");;;
        break: #()
      else do:  #());;;
      do:  ("i" <-[#uint64T] ((![#uint64T] "i") + #(W64 1)));;;
      continue: #());;;
    return: (![#boolT] "retval")).

(* See the [reference].

   [reference]: https://pkg.go.dev/bytes#Clone

   go: goose_std.go:38:6 *)
Definition BytesClone : val :=
  rec: "BytesClone" "b" :=
    exception_do (let: "b" := (alloc "b") in
    (if: (![#sliceT] "b") = #slice.nil
    then return: (#slice.nil)
    else do:  #());;;
    return: (let: "$a0" := #slice.nil in
     let: "$a1" := (![#sliceT] "b") in
     (slice.append #byteT) "$a0" "$a1")).

(* SliceSplit splits xs at n into two slices.

   The capacity of the first slice overlaps with the second, so afterward it is
   no longer safe to append to the first slice.

   TODO: once goose supports it, make this function generic in the slice element
   type

   go: goose_std.go:52:6 *)
Definition SliceSplit : val :=
  rec: "SliceSplit" "xs" "n" :=
    exception_do (let: "n" := (alloc "n") in
    let: "xs" := (alloc "xs") in
    return: (let: "$s" := (![#sliceT] "xs") in
     slice.slice #byteT "$s" #(W64 0) (![#uint64T] "n"), let: "$s" := (![#sliceT] "xs") in
     slice.slice #byteT "$s" (![#uint64T] "n") (slice.len "$s"))).

(* Returns true if x + y does not overflow

   go: goose_std.go:60:6 *)
Definition SumNoOverflow : val :=
  rec: "SumNoOverflow" "x" "y" :=
    exception_do (let: "y" := (alloc "y") in
    let: "x" := (alloc "x") in
    return: (((![#uint64T] "x") + (![#uint64T] "y")) ≥ (![#uint64T] "x"))).

(* SumAssumeNoOverflow returns x + y, `Assume`ing that this does not overflow.

   *Use with care* - if the assumption is violated this function will panic.

   go: goose_std.go:67:6 *)
Definition SumAssumeNoOverflow : val :=
  rec: "SumAssumeNoOverflow" "x" "y" :=
    exception_do (let: "y" := (alloc "y") in
    let: "x" := (alloc "x") in
    do:  (let: "$a0" := (let: "$a0" := (![#uint64T] "x") in
    let: "$a1" := (![#uint64T] "y") in
    (func_call #std.std #"SumNoOverflow"%go) "$a0" "$a1") in
    (func_call #primitive #"Assume"%go) "$a0");;;
    return: ((![#uint64T] "x") + (![#uint64T] "y"))).

(* MulNoOverflow returns true if x * y does not overflow

   go: goose_std.go:73:6 *)
Definition MulNoOverflow : val :=
  rec: "MulNoOverflow" "x" "y" :=
    exception_do (let: "y" := (alloc "y") in
    let: "x" := (alloc "x") in
    (if: ((![#uint64T] "x") = #(W64 0)) || ((![#uint64T] "y") = #(W64 0))
    then return: (#true)
    else do:  #());;;
    return: ((![#uint64T] "x") ≤ (#(W64 (18446744073709551616 - 1)) `quot` (![#uint64T] "y")))).

(* MulAssumeNoOverflow returns x * y, `Assume`ing that this does not overflow.

   *Use with care* - if the assumption is violated this function will panic.

   go: goose_std.go:83:6 *)
Definition MulAssumeNoOverflow : val :=
  rec: "MulAssumeNoOverflow" "x" "y" :=
    exception_do (let: "y" := (alloc "y") in
    let: "x" := (alloc "x") in
    do:  (let: "$a0" := (let: "$a0" := (![#uint64T] "x") in
    let: "$a1" := (![#uint64T] "y") in
    (func_call #std.std #"MulNoOverflow"%go) "$a0" "$a1") in
    (func_call #primitive #"Assume"%go) "$a0");;;
    return: ((![#uint64T] "x") * (![#uint64T] "y"))).

Definition JoinHandle : go_type := structT [
  "mu" :: ptrT;
  "done" :: boolT;
  "cond" :: ptrT
].

(* go: goose_std.go:96:6 *)
Definition newJoinHandle : val :=
  rec: "newJoinHandle" <> :=
    exception_do (let: "mu" := (alloc (type.zero_val #ptrT)) in
    let: "$r0" := (alloc (type.zero_val #sync.Mutex)) in
    do:  ("mu" <-[#ptrT] "$r0");;;
    let: "cond" := (alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := (interface.make #sync #"Mutex'ptr" (![#ptrT] "mu")) in
    (func_call #sync #"NewCond"%go) "$a0") in
    do:  ("cond" <-[#ptrT] "$r0");;;
    return: (alloc (let: "$mu" := (![#ptrT] "mu") in
     let: "$done" := #false in
     let: "$cond" := (![#ptrT] "cond") in
     struct.make JoinHandle [{
       "mu" ::= "$mu";
       "done" ::= "$done";
       "cond" ::= "$cond"
     }]))).

(* go: goose_std.go:106:22 *)
Definition JoinHandle__finish : val :=
  rec: "JoinHandle__finish" "h" <> :=
    exception_do (let: "h" := (alloc "h") in
    do:  ((method_call #sync #"Mutex'ptr" #"Lock" (![#ptrT] (struct.field_ref JoinHandle "mu" (![#ptrT] "h")))) #());;;
    let: "$r0" := #true in
    do:  ((struct.field_ref JoinHandle "done" (![#ptrT] "h")) <-[#boolT] "$r0");;;
    do:  ((method_call #sync #"Cond'ptr" #"Signal" (![#ptrT] (struct.field_ref JoinHandle "cond" (![#ptrT] "h")))) #());;;
    do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] (struct.field_ref JoinHandle "mu" (![#ptrT] "h")))) #())).

(* Spawn runs `f` in a parallel goroutine and returns a handle to wait for
   it to finish.

   Due to Goose limitations we do not return anything from the function, but it
   could return an `interface{}` value or be generic in the return value with
   essentially the same implementation, replacing `done` with a pointer to the
   result value.

   go: goose_std.go:120:6 *)
Definition Spawn : val :=
  rec: "Spawn" "f" :=
    exception_do (let: "f" := (alloc "f") in
    let: "h" := (alloc (type.zero_val #ptrT)) in
    let: "$r0" := ((func_call #std.std #"newJoinHandle"%go) #()) in
    do:  ("h" <-[#ptrT] "$r0");;;
    let: "$go" := (λ: <>,
      exception_do (do:  ((![#funcT] "f") #());;;
      do:  ((method_call #std.std #"JoinHandle'ptr" #"finish" (![#ptrT] "h")) #()))
      ) in
    do:  (Fork ("$go" #()));;;
    return: (![#ptrT] "h")).

(* go: goose_std.go:129:22 *)
Definition JoinHandle__Join : val :=
  rec: "JoinHandle__Join" "h" <> :=
    exception_do (let: "h" := (alloc "h") in
    do:  ((method_call #sync #"Mutex'ptr" #"Lock" (![#ptrT] (struct.field_ref JoinHandle "mu" (![#ptrT] "h")))) #());;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: ![#boolT] (struct.field_ref JoinHandle "done" (![#ptrT] "h"))
      then
        let: "$r0" := #false in
        do:  ((struct.field_ref JoinHandle "done" (![#ptrT] "h")) <-[#boolT] "$r0");;;
        break: #()
      else do:  #());;;
      do:  ((method_call #sync #"Cond'ptr" #"Wait" (![#ptrT] (struct.field_ref JoinHandle "cond" (![#ptrT] "h")))) #()));;;
    do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] (struct.field_ref JoinHandle "mu" (![#ptrT] "h")))) #())).

(* Multipar runs op(0) ... op(num-1) in parallel and waits for them all to finish.

   Implementation note: does not use a done channel (which is the standard
   pattern in Go) because this is not supported by Goose. Instead uses mutexes
   and condition variables since these are modeled in Goose

   go: goose_std.go:148:6 *)
Definition Multipar : val :=
  rec: "Multipar" "num" "op" :=
    exception_do (let: "op" := (alloc "op") in
    let: "num" := (alloc "num") in
    let: "num_left" := (alloc (type.zero_val #uint64T)) in
    let: "$r0" := (![#uint64T] "num") in
    do:  ("num_left" <-[#uint64T] "$r0");;;
    let: "num_left_mu" := (alloc (type.zero_val #ptrT)) in
    let: "$r0" := (alloc (type.zero_val #sync.Mutex)) in
    do:  ("num_left_mu" <-[#ptrT] "$r0");;;
    let: "num_left_cond" := (alloc (type.zero_val #ptrT)) in
    let: "$r0" := (let: "$a0" := (interface.make #sync #"Mutex'ptr" (![#ptrT] "num_left_mu")) in
    (func_call #sync #"NewCond"%go) "$a0") in
    do:  ("num_left_cond" <-[#ptrT] "$r0");;;
    (let: "i" := (alloc (type.zero_val #uint64T)) in
    let: "$r0" := #(W64 0) in
    do:  ("i" <-[#uint64T] "$r0");;;
    (for: (λ: <>, (![#uint64T] "i") < (![#uint64T] "num")); (λ: <>, do:  ("i" <-[#uint64T] ((![#uint64T] "i") + #(W64 1)))) := λ: <>,
      let: "i" := (alloc (type.zero_val #uint64T)) in
      let: "$r0" := (![#uint64T] "i") in
      do:  ("i" <-[#uint64T] "$r0");;;
      let: "$go" := (λ: <>,
        exception_do (do:  (let: "$a0" := (![#uint64T] "i") in
        (![#funcT] "op") "$a0");;;
        do:  ((method_call #sync #"Mutex'ptr" #"Lock" (![#ptrT] "num_left_mu")) #());;;
        do:  ("num_left" <-[#uint64T] ((![#uint64T] "num_left") - #(W64 1)));;;
        do:  ((method_call #sync #"Cond'ptr" #"Signal" (![#ptrT] "num_left_cond")) #());;;
        do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] "num_left_mu")) #()))
        ) in
      do:  (Fork ("$go" #()))));;;
    do:  ((method_call #sync #"Mutex'ptr" #"Lock" (![#ptrT] "num_left_mu")) #());;;
    (for: (λ: <>, (![#uint64T] "num_left") > #(W64 0)); (λ: <>, Skip) := λ: <>,
      do:  ((method_call #sync #"Cond'ptr" #"Wait" (![#ptrT] "num_left_cond")) #()));;;
    do:  ((method_call #sync #"Mutex'ptr" #"Unlock" (![#ptrT] "num_left_mu")) #())).

(* Skip is a no-op that can be useful in proofs.

   Occasionally a proof may need to open an invariant and perform a ghost update
   across a step in the operational semantics. The GooseLang model may not have
   a convenient step, but it is always sound to insert more. Calling std.Skip()
   is a simple way to do so - the model always requires one step to reduce this
   application to a value.

   go: goose_std.go:179:6 *)
Definition Skip : val :=
  rec: "Skip" <> :=
    exception_do (do:  #()).

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("Assert"%go, Assert); ("BytesEqual"%go, BytesEqual); ("BytesClone"%go, BytesClone); ("SliceSplit"%go, SliceSplit); ("SumNoOverflow"%go, SumNoOverflow); ("SumAssumeNoOverflow"%go, SumAssumeNoOverflow); ("MulNoOverflow"%go, MulNoOverflow); ("MulAssumeNoOverflow"%go, MulAssumeNoOverflow); ("newJoinHandle"%go, newJoinHandle); ("Spawn"%go, Spawn); ("Multipar"%go, Multipar); ("Skip"%go, Skip)].

Definition msets' : list (go_string * (list (go_string * val))) := [("JoinHandle"%go, []); ("JoinHandle'ptr"%go, [("Join"%go, JoinHandle__Join); ("finish"%go, JoinHandle__finish)])].

#[global] Instance info' : PkgInfo std.std :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [sync; primitive];
  |}.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init std.std (λ: <>,
      exception_do (do:  primitive.initialize';;;
      do:  sync.initialize')
      ).

End code.
End std.
