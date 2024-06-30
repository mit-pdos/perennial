From Goose Require Import sync.
From Perennial.goose_lang Require Export ffi.grove_ffi.impl notation.
From Perennial.new_goose_lang Require Import prelude typing.impl.
From Perennial.goose_lang.lib Require time.impl.

Section code.
Context `{ffi_syntax}.
Local Coercion Var' s: expr := Var s.

Definition Assume: val := control.impl.Assume.
Definition Assert: val := control.impl.Assert.
Definition Exit: val := control.impl.Exit.

  Definition EncodeUInt32: val :=
    λ: "n" "p",
    "p" +ₗ #0 <-[uint8T] to_u8 ("n" ≫ #(W32 $ 0*8));;
    "p" +ₗ #1 <-[uint8T] to_u8 ("n" ≫ #(W32 $ 1*8));;
    "p" +ₗ #2 <-[uint8T] to_u8 ("n" ≫ #(W32 $ 2*8));;
    "p" +ₗ #3 <-[uint8T] to_u8 ("n" ≫ #(W32 $ 3*8)).

  Definition DecodeUInt32: val :=
    λ: "p",
    let: "v0" := to_u32 ![uint8T]"p" in
    let: "v1" := to_u32 ![uint8T]("p" +ₗ #1) in
    let: "v2" := to_u32 ![uint8T]("p" +ₗ #2) in
    let: "v3" := to_u32 ![uint8T]("p" +ₗ #3) in
    "v0" `or` ("v1" `or` ("v2" `or` "v3" ≪ #(W32 8)) ≪ #(W32 8)) ≪ #(W32 8).

  Definition EncodeUInt64: val :=
    λ: "n" "p",
    "p" +ₗ #0 <-[uint8T] to_u8 ("n" ≫ #(0*8));;
    "p" +ₗ #1 <-[uint8T] to_u8 ("n" ≫ #(1*8));;
    "p" +ₗ #2 <-[uint8T] to_u8 ("n" ≫ #(2*8));;
    "p" +ₗ #3 <-[uint8T] to_u8 ("n" ≫ #(3*8));;
    "p" +ₗ #4 <-[uint8T] to_u8 ("n" ≫ #(4*8));;
    "p" +ₗ #5 <-[uint8T] to_u8 ("n" ≫ #(5*8));;
    "p" +ₗ #6 <-[uint8T] to_u8 ("n" ≫ #(6*8));;
    "p" +ₗ #7 <-[uint8T] to_u8 ("n" ≫ #(7*8))
  .

  Definition DecodeUInt64: val :=
    λ: "p",
    let: "v0" := to_u64 ![uint8T]"p" in
    let: "v1" := to_u64 ![uint8T]("p" +ₗ #1) in
    let: "v2" := to_u64 ![uint8T]("p" +ₗ #2) in
    let: "v3" := to_u64 ![uint8T]("p" +ₗ #3) in
    let: "v4" := to_u64 ![uint8T]("p" +ₗ #4) in
    let: "v5" := to_u64 ![uint8T]("p" +ₗ #5) in
    let: "v6" := to_u64 ![uint8T]("p" +ₗ #6) in
    let: "v7" := to_u64 ![uint8T]("p" +ₗ #7) in
    "v0" `or` ("v1" `or` ("v2" `or` ("v3" `or` ("v4" `or` ("v5" `or` ("v6" `or` "v7"
      ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8).

  Definition UInt64Put: val :=
    λ: "p" "n",
    EncodeUInt64 "n" (slice.ptr "p").

  Definition UInt64Get: val :=
    λ: "p",
    DecodeUInt64 (slice.ptr "p").

  Definition UInt32Put: val :=
    λ: "p" "n",
    EncodeUInt32 "n" (slice.ptr "p").

  Definition UInt32Get: val :=
    λ: "p",
    DecodeUInt32 (slice.ptr "p").

  Definition Millisecond: val := #1000000.
  Definition Second: val := #1000000000.
  Definition Sleep: val := λ: "duration", #().
  Definition TimeNow: val := λ: <>, ArbitraryInt.
  Definition AfterFunc: val := λ: "duration" "f", Fork "f" ;; ref "f".
  Definition Timer__Reset: val := λ: <>, #().
  Definition WaitTimeout: val := λ: "l" "timeout", sync.Cond__Wait "l".

  Definition RandomUint64: val := λ: <>, ArbitraryInt.
  Definition NewProph : val := λ: <>, NewProph.
  Definition ResolveProph : val :=
    λ: "p" "val", ResolveProph (Var "p") (Var "val").
  Definition Linearize := Linearize.
End code.
