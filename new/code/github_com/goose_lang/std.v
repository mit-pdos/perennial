(* autogenerated from github.com/goose-lang/std *)
From New.golang Require Import defn.
From New.code Require github_com.goose_lang.primitive.
From New.code Require sync.

Section code.
Context `{ffi_syntax}.
Local Coercion Var' s: expr := Var s.

(* BytesEqual returns if the two byte slices are equal.

   go: goose_std.go:10:6 *)
Definition BytesEqual : val :=
  rec: "BytesEqual" "x" "y" :=
    exception_do (let: "y" := ref_ty (sliceT byteT) "y" in
    let: "x" := ref_ty (sliceT byteT) "x" in
    let: "xlen" := ref_ty intT (zero_val intT) in
    let: "$r0" := slice.len (![sliceT byteT] "x") in
    do:  ("xlen" <-[intT] "$r0");;;
    (if: (![intT] "xlen") ≠ (slice.len (![sliceT byteT] "y"))
    then
      return: (#false);;;
      do:  #()
    else do:  #());;;
    let: "i" := ref_ty uint64T #0 in
    let: "retval" := ref_ty boolT #true in
    (for: (λ: <>, (![uint64T] "i") < (![intT] "xlen")); (λ: <>, Skip) := λ: <>,
      (if: (![byteT] (slice.elem_ref byteT (![sliceT byteT] "x") (![uint64T] "i"))) ≠ (![byteT] (slice.elem_ref byteT (![sliceT byteT] "y") (![uint64T] "i")))
      then
        let: "$r0" := #false in
        do:  ("retval" <-[boolT] "$r0");;;
        break: #();;;
        do:  #()
      else do:  #());;;
      do:  ("i" <-[uint64T] ((![uint64T] "i") + #1));;;
      continue: #();;;
      do:  #());;;
    return: (![boolT] "retval");;;
    do:  #()).

(* See the [reference].

   [reference]: https://pkg.go.dev/bytes#Clone

   go: goose_std.go:31:6 *)
Definition BytesClone : val :=
  rec: "BytesClone" "b" :=
    exception_do (let: "b" := ref_ty (sliceT byteT) "b" in
    (if: (![sliceT byteT] "b") = slice.nil
    then
      return: (slice.nil);;;
      do:  #()
    else do:  #());;;
    return: (slice.append byteT slice.nil (![sliceT byteT] "b"));;;
    do:  #()).

(* SliceSplit splits xs at n into two slices.

   The capacity of the first slice overlaps with the second, so afterward it is
   no longer safe to append to the first slice.

   TODO: once goose supports it, make this function generic in the slice element
   type

   go: goose_std.go:45:6 *)
Definition SliceSplit : val :=
  rec: "SliceSplit" "xs" "n" :=
    exception_do (let: "n" := ref_ty uint64T "n" in
    let: "xs" := ref_ty (sliceT byteT) "xs" in
    return: (let: "$s" := ![sliceT byteT] "xs" in
     slice.slice byteT "$s" #0 (![uint64T] "n"), let: "$s" := ![sliceT byteT] "xs" in
     slice.slice byteT "$s" (![uint64T] "n") (slice.len "$s"));;;
    do:  #()).

(* Returns true if x + y does not overflow

   go: goose_std.go:53:6 *)
Definition SumNoOverflow : val :=
  rec: "SumNoOverflow" "x" "y" :=
    exception_do (let: "y" := ref_ty uint64T "y" in
    let: "x" := ref_ty uint64T "x" in
    return: (((![uint64T] "x") + (![uint64T] "y")) ≥ (![uint64T] "x"));;;
    do:  #()).

(* SumAssumeNoOverflow returns x + y, `Assume`ing that this does not overflow.

   *Use with care* - if the assumption is violated this function will panic.

   go: goose_std.go:60:6 *)
Definition SumAssumeNoOverflow : val :=
  rec: "SumAssumeNoOverflow" "x" "y" :=
    exception_do (let: "y" := ref_ty uint64T "y" in
    let: "x" := ref_ty uint64T "x" in
    do:  (let: "$a0" := let: "$a0" := ![uint64T] "x" in
    let: "$a1" := ![uint64T] "y" in
    SumNoOverflow "$a0" "$a1" in
    primitive.Assume "$a0");;;
    return: ((![uint64T] "x") + (![uint64T] "y"));;;
    do:  #()).

Definition JoinHandle : go_type := structT [
  "mu" :: ptrT;
  "done" :: boolT;
  "cond" :: ptrT
].

Definition JoinHandle__mset : list (string * val) := [
].

(* go: goose_std.go:106:22 *)
Definition JoinHandle__Join : val :=
  rec: "JoinHandle__Join" "h" <> :=
    exception_do (let: "h" := ref_ty ptrT "h" in
    do:  ((sync.Mutex__Lock (![ptrT] (struct.field_ref JoinHandle "mu" (![ptrT] "h")))) #());;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: ![boolT] (struct.field_ref JoinHandle "done" (![ptrT] "h"))
      then
        let: "$r0" := #false in
        do:  ((struct.field_ref JoinHandle "done" (![ptrT] "h")) <-[boolT] "$r0");;;
        break: #();;;
        do:  #()
      else do:  #());;;
      do:  ((sync.Cond__Wait (![ptrT] (struct.field_ref JoinHandle "cond" (![ptrT] "h")))) #());;;
      do:  #());;;
    do:  ((sync.Mutex__Unlock (![ptrT] (struct.field_ref JoinHandle "mu" (![ptrT] "h")))) #());;;
    do:  #()).

(* go: goose_std.go:83:22 *)
Definition JoinHandle__finish : val :=
  rec: "JoinHandle__finish" "h" <> :=
    exception_do (let: "h" := ref_ty ptrT "h" in
    do:  ((sync.Mutex__Lock (![ptrT] (struct.field_ref JoinHandle "mu" (![ptrT] "h")))) #());;;
    let: "$r0" := #true in
    do:  ((struct.field_ref JoinHandle "done" (![ptrT] "h")) <-[boolT] "$r0");;;
    do:  ((sync.Cond__Signal (![ptrT] (struct.field_ref JoinHandle "cond" (![ptrT] "h")))) #());;;
    do:  ((sync.Mutex__Unlock (![ptrT] (struct.field_ref JoinHandle "mu" (![ptrT] "h")))) #());;;
    do:  #()).

Definition JoinHandle__mset_ptr : list (string * val) := [
  ("Join", JoinHandle__Join);
  ("finish", JoinHandle__finish)
].

(* go: goose_std.go:73:6 *)
Definition newJoinHandle : val :=
  rec: "newJoinHandle" <> :=
    exception_do (let: "mu" := ref_ty ptrT (zero_val ptrT) in
    let: "$r0" := ref_ty sync.Mutex (zero_val sync.Mutex) in
    do:  ("mu" <-[ptrT] "$r0");;;
    let: "cond" := ref_ty ptrT (zero_val ptrT) in
    let: "$r0" := let: "$a0" := interface.make sync.Mutex__mset_ptr (![ptrT] "mu") in
    sync.NewCond "$a0" in
    do:  ("cond" <-[ptrT] "$r0");;;
    return: (ref_ty JoinHandle (struct.make JoinHandle [{
       "mu" ::= ![ptrT] "mu";
       "done" ::= #false;
       "cond" ::= ![ptrT] "cond"
     }]));;;
    do:  #()).

(* Spawn runs `f` in a parallel goroutine and returns a handle to wait for
   it to finish.

   Due to Goose limitations we do not return anything from the function, but it
   could return an `interface{}` value or be generic in the return value with
   essentially the same implementation, replacing `done` with a pointer to the
   result value.

   go: goose_std.go:97:6 *)
Definition Spawn : val :=
  rec: "Spawn" "f" :=
    exception_do (let: "f" := ref_ty funcT "f" in
    let: "h" := ref_ty ptrT (zero_val ptrT) in
    let: "$r0" := newJoinHandle #() in
    do:  ("h" <-[ptrT] "$r0");;;
    let: "$go" := (λ: <>,
      do:  ((![funcT] "f") #());;;
      do:  ((JoinHandle__finish (![ptrT] "h")) #());;;
      do:  #()
      ) in
    do:  (Fork ("$go" #()));;;
    return: (![ptrT] "h");;;
    do:  #()).

(* Multipar runs op(0) ... op(num-1) in parallel and waits for them all to finish.

   Implementation note: does not use a done channel (which is the standard
   pattern in Go) because this is not supported by Goose. Instead uses mutexes
   and condition variables since these are modeled in Goose

   go: goose_std.go:125:6 *)
Definition Multipar : val :=
  rec: "Multipar" "num" "op" :=
    exception_do (let: "op" := ref_ty funcT "op" in
    let: "num" := ref_ty uint64T "num" in
    let: "num_left" := ref_ty uint64T (![uint64T] "num") in
    let: "num_left_mu" := ref_ty ptrT (zero_val ptrT) in
    let: "$r0" := ref_ty sync.Mutex (zero_val sync.Mutex) in
    do:  ("num_left_mu" <-[ptrT] "$r0");;;
    let: "num_left_cond" := ref_ty ptrT (zero_val ptrT) in
    let: "$r0" := let: "$a0" := interface.make sync.Mutex__mset_ptr (![ptrT] "num_left_mu") in
    sync.NewCond "$a0" in
    do:  ("num_left_cond" <-[ptrT] "$r0");;;
    (let: "i" := ref_ty uint64T (zero_val uint64T) in
    let: "$r0" := #0 in
    do:  ("i" <-[uint64T] "$r0");;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "num")); (λ: <>, do:  ("i" <-[uint64T] ((![uint64T] "i") + #1));;;
    #()) := λ: <>,
      let: "i" := ref_ty uint64T (zero_val uint64T) in
      let: "$r0" := ![uint64T] "i" in
      do:  ("i" <-[uint64T] "$r0");;;
      let: "$go" := (λ: <>,
        do:  (let: "$a0" := ![uint64T] "i" in
        (![funcT] "op") "$a0");;;
        do:  ((sync.Mutex__Lock (![ptrT] "num_left_mu")) #());;;
        do:  ("num_left" <-[uint64T] ((![uint64T] "num_left") - #1));;;
        do:  ((sync.Cond__Signal (![ptrT] "num_left_cond")) #());;;
        do:  ((sync.Mutex__Unlock (![ptrT] "num_left_mu")) #());;;
        do:  #()
        ) in
      do:  (Fork ("$go" #()));;;
      do:  #()));;;
    do:  ((sync.Mutex__Lock (![ptrT] "num_left_mu")) #());;;
    (for: (λ: <>, (![uint64T] "num_left") > #0); (λ: <>, Skip) := λ: <>,
      do:  ((sync.Cond__Wait (![ptrT] "num_left_cond")) #());;;
      do:  #());;;
    do:  ((sync.Mutex__Unlock (![ptrT] "num_left_mu")) #());;;
    do:  #()).

(* Skip is a no-op that can be useful in proofs.

   Occasionally a proof may need to open an invariant and perform a ghost update
   across a step in the operational semantics. The GooseLang model may not have
   a convenient step, but it is always sound to insert more. Calling std.Skip()
   is a simple way to do so - the model always requires one step to reduce this
   application to a value.

   go: goose_std.go:156:6 *)
Definition Skip : val :=
  rec: "Skip" <> :=
    exception_do (do:  #()).

End code.
