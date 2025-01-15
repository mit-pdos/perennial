From New.code Require Import sync.
From New.golang Require Import defn.

Section code.
  Context `{ffi_syntax}.

  Definition pkg_name' : go_string := "github.com/mit-pdos/goose_lang/primitive".

  (** [Assume c] goes into an endless loop if [c] does not hold. So proofs can
assume that it holds. *)
  Definition Assume : (go_string * go_string) := (pkg_name', "Assume"%go).
  Definition Assume' : val :=
    λ: "cond", if: Var "cond" then #()
               else (rec: "loop" <> := Var "loop" #()) #().

  (** [Assert c] raises UB (program gets stuck via [Panic]) if [c] does not
hold. So proofs have to show it always holds. *)
  Definition Assert : (go_string * go_string) := (pkg_name', "Assert"%go).
  Definition Assert' : val :=
    λ: "cond", if: Var "cond" then #()
               else Panic "assert failed".

  (** [Exit n] is supposed to exit the process. We cannot directly model
this in GooseLang, so we just loop. *)
  Definition Exit : (go_string * go_string) := (pkg_name', "Exit"%go).
  Definition Exit' : val :=
    λ: <>, (rec: "loop" <> := Var "loop" #()) #().

  Definition UInt64Put : (go_string * go_string) := (pkg_name', "UInt64Put"%go).
  Definition UInt64Put': val := λ: "p" "n",
      do: (slice.elem_ref uint8T "p" #(W64 0)) <-[uint8T] to_u8 ("n" ≫ #(W64 (0*8)));;;
      do: (slice.elem_ref uint8T "p" #(W64 1)) <-[uint8T] to_u8 ("n" ≫ #(W64 (1*8)));;;
      do: (slice.elem_ref uint8T "p" #(W64 2)) <-[uint8T] to_u8 ("n" ≫ #(W64 (2*8)));;;
      do: (slice.elem_ref uint8T "p" #(W64 3)) <-[uint8T] to_u8 ("n" ≫ #(W64 (3*8)));;;
      do: (slice.elem_ref uint8T "p" #(W64 4)) <-[uint8T] to_u8 ("n" ≫ #(W64 (4*8)));;;
      do: (slice.elem_ref uint8T "p" #(W64 5)) <-[uint8T] to_u8 ("n" ≫ #(W64 (5*8)));;;
      do: (slice.elem_ref uint8T "p" #(W64 6)) <-[uint8T] to_u8 ("n" ≫ #(W64 (6*8)));;;
      do: (slice.elem_ref uint8T "p" #(W64 7)) <-[uint8T] to_u8 ("n" ≫ #(W64 (7*8)))
    .

  Definition UInt64Get : (go_string * go_string) := (pkg_name', "UInt64Get"%go).
  Definition UInt64Get': val := λ: "p",
      let: "v0" := to_u64 ![uint8T](slice.elem_ref uint8T "p" #(W64 0)) in
      let: "v1" := to_u64 ![uint8T](slice.elem_ref uint8T "p" #(W64 1)) in
      let: "v2" := to_u64 ![uint8T](slice.elem_ref uint8T "p" #(W64 2)) in
      let: "v3" := to_u64 ![uint8T](slice.elem_ref uint8T "p" #(W64 3)) in
      let: "v4" := to_u64 ![uint8T](slice.elem_ref uint8T "p" #(W64 4)) in
      let: "v5" := to_u64 ![uint8T](slice.elem_ref uint8T "p" #(W64 5)) in
      let: "v6" := to_u64 ![uint8T](slice.elem_ref uint8T "p" #(W64 6)) in
      let: "v7" := to_u64 ![uint8T](slice.elem_ref uint8T "p" #(W64 7)) in
      "v0" `or` ("v1" `or` ("v2" `or` ("v3" `or` ("v4" `or` ("v5" `or` ("v6" `or` "v7"
          ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8).

  Definition UInt32Put : (go_string * go_string) := (pkg_name', "UInt32Put"%go).
  Definition UInt32Put': val :=
    λ: "p" "n",
      do: (slice.elem_ref uint8T "p" #(W64 0)) <-[uint8T] to_u8 ("n" ≫ #(W32 (0*8)));;;
      do: (slice.elem_ref uint8T "p" #(W64 1)) <-[uint8T] to_u8 ("n" ≫ #(W32 (1*8)));;;
      do: (slice.elem_ref uint8T "p" #(W64 2)) <-[uint8T] to_u8 ("n" ≫ #(W32 (2*8)));;;
      do: (slice.elem_ref uint8T "p" #(W64 3)) <-[uint8T] to_u8 ("n" ≫ #(W32 (3*8)))
    .

  Definition UInt32Get : (go_string * go_string) := (pkg_name', "UInt32Get"%go).
  Definition UInt32Get' : val := λ: "p",
      let: "v0" := to_u32 ![uint8T](slice.elem_ref uint8T "p" #(W64 0)) in
      let: "v1" := to_u32 ![uint8T](slice.elem_ref uint8T "p" #(W64 1)) in
      let: "v2" := to_u32 ![uint8T](slice.elem_ref uint8T "p" #(W64 2)) in
      let: "v3" := to_u32 ![uint8T](slice.elem_ref uint8T "p" #(W64 3)) in
      "v0" `or` ("v1" `or` ("v2" `or` ("v3" ≪ #(W32 8)) ≪ #(W32 8)) ≪ #(W32 8)) ≪ #(W32 8).

  Definition Millisecond: val := #(W64 1000000).
  Definition Second: val := #(W64 1000000000).

  Definition Sleep : (go_string * go_string) := (pkg_name', "Sleep"%go).
  Definition Sleep' : val := λ: "duration", #().

  Definition TimeNow : (go_string * go_string) := (pkg_name', "TimeNow"%go).
  Definition TimeNow' : val := λ: <>, ArbitraryInt.

  Definition AfterFunc : (go_string * go_string) := (pkg_name', "AfterFunc"%go).
  Definition AfterFunc' : val := λ: "duration" "f", Fork "f" ;; ref "f".

  Definition WaitTimeout : (go_string * go_string) := (pkg_name', "WaitTimeout"%go).
  Definition WaitTimeout' : val := λ: "l" "timeout", method_call #sync.pkg_name' #"Cond" "Wait" "l".

  Definition RandomUint64 : (go_string * go_string) := (pkg_name', "RandomUint64"%go).
  Definition RandomUint64' : val := λ: <>, ArbitraryInt.

  Definition NewProph : (go_string * go_string) := (pkg_name', "NewProph"%go).
  Definition NewProph' : val := λ: <>, goose_lang.NewProph.

  Definition ResolveProph : (go_string * go_string) := (pkg_name', "ResolveProph"%go).
  Definition ResolveProph' : val := λ: "p" "val", goose_lang.ResolveProph (Var "p") (Var "val").

  Definition Linearize : (go_string * go_string) := (pkg_name', "Linearize"%go).
  Definition Linearize' : val := λ: <>, #().

  Definition vars' : list (go_string * go_type) := [].
  Definition functions' : list (go_string * val) := [].
  Definition msets' : list (go_string * (list (go_string * val))) := [].
  Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' vars' functions' msets' (λ: <>,
      exception_do (do:  sync.initialize')
      ).

End code.
