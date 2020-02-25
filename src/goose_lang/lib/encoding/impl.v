From iris.proofmode Require Import tactics.
From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import typed_mem.impl slice.impl map.impl.

Set Default Proof Using "Type".

Section goose_lang.
  Context {ext} {ext_ty:ext_types ext}.

  Definition Var' s : @expr ext := Var s.
  Local Coercion Var' : string >-> expr.

  Definition EncodeUInt32: val :=
    λ: "n" "p",
    "p" +ₗ #0 <-[u8T] to_u8 ("n" ≫ #(U32 $ 0*8));;
    "p" +ₗ #1 <-[u8T] to_u8 ("n" ≫ #(U32 $ 1*8));;
    "p" +ₗ #2 <-[u8T] to_u8 ("n" ≫ #(U32 $ 2*8));;
    "p" +ₗ #3 <-[u8T] to_u8 ("n" ≫ #(U32 $ 3*8)).

  Definition DecodeUInt32: val :=
    λ: "p",
    let: "v0" := to_u32 ![u8T]"p" in
    let: "v1" := to_u32 ![u8T]("p" +ₗ #1) in
    let: "v2" := to_u32 ![u8T]("p" +ₗ #2) in
    let: "v3" := to_u32 ![u8T]("p" +ₗ #3) in
    "v0" ∥ ("v1" ∥ ("v2" ∥ "v3" ≪ #(U32 8)) ≪ #(U32 8)) ≪ #(U32 8).

  Definition EncodeUInt64: val :=
    λ: "n" "p",
    "p" +ₗ #0 <-[u8T] to_u8 ("n" ≫ #(0*8));;
    "p" +ₗ #1 <-[u8T] to_u8 ("n" ≫ #(1*8));;
    "p" +ₗ #2 <-[u8T] to_u8 ("n" ≫ #(2*8));;
    "p" +ₗ #3 <-[u8T] to_u8 ("n" ≫ #(3*8));;
    "p" +ₗ #4 <-[u8T] to_u8 ("n" ≫ #(4*8));;
    "p" +ₗ #5 <-[u8T] to_u8 ("n" ≫ #(5*8));;
    "p" +ₗ #6 <-[u8T] to_u8 ("n" ≫ #(6*8));;
    "p" +ₗ #7 <-[u8T] to_u8 ("n" ≫ #(7*8))
  .

  Definition DecodeUInt64: val :=
    λ: "p",
    let: "v0" := to_u64 ![u8T]"p" in
    let: "v1" := to_u64 ![u8T]("p" +ₗ #1) in
    let: "v2" := to_u64 ![u8T]("p" +ₗ #2) in
    let: "v3" := to_u64 ![u8T]("p" +ₗ #3) in
    let: "v4" := to_u64 ![u8T]("p" +ₗ #4) in
    let: "v5" := to_u64 ![u8T]("p" +ₗ #5) in
    let: "v6" := to_u64 ![u8T]("p" +ₗ #6) in
    let: "v7" := to_u64 ![u8T]("p" +ₗ #7) in
    "v0" ∥ ("v1" ∥ ("v2" ∥ ("v3" ∥ ("v4" ∥ ("v5" ∥ ("v6" ∥ "v7"
      ≪ #(U64 8)) ≪ #(U64 8)) ≪ #(U64 8)) ≪ #(U64 8)) ≪ #(U64 8)) ≪ #(U64 8)) ≪ #(U64 8).

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

End goose_lang.
