From iris.proofmode Require Import tactics.
From Perennial.goose_lang Require Import struct typing slice map.

Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ext_semantics}.
  Context {ext_ty:ext_types ext}.

  Definition Var' s : @expr ext := Var s.
  Local Coercion Var' : string >-> expr.

  Definition EncodeUInt32: val :=
    λ: "n" "p",
    "p" +ₗ #0 <-[u8T] to_u8 ("n" ≫ #(U32 $ 0*8));;
    "p" +ₗ #1 <-[u8T] to_u8 ("n" ≫ #(U32 $ 1*8));;
    "p" +ₗ #2 <-[u8T] to_u8 ("n" ≫ #(U32 $ 2*8));;
    "p" +ₗ #3 <-[u8T] to_u8 ("n" ≫ #(U32 $ 3*8)).

  Theorem EncodeUInt32_t : (⊢ EncodeUInt32 : (uint32T -> arrayT byteT -> unitT))%T.
  Proof.
    typecheck.
  Qed.

  Definition DecodeUInt32: val :=
    λ: "p",
    let: "v0" := to_u32 ![u8T]"p" in
    let: "v1" := to_u32 ![u8T]("p" +ₗ #1) in
    let: "v2" := to_u32 ![u8T]("p" +ₗ #2) in
    let: "v3" := to_u32 ![u8T]("p" +ₗ #3) in
    "v0" ∥ ("v1" ∥ ("v2" ∥ "v3" ≪ #(U32 8)) ≪ #(U32 8)) ≪ #(U32 8).

  Theorem DecodeUInt32_t : (⊢ DecodeUInt32 : (arrayT byteT -> uint32T))%T.
  Proof.
    typecheck.
  Qed.

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

  Theorem EncodeUInt64_t : (⊢ EncodeUInt64 : (uint64T -> arrayT byteT -> unitT))%T.
  Proof.
    typecheck.
  Qed.

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

  Theorem DecodeUInt64_t : (⊢ DecodeUInt64 : (arrayT byteT -> uint64T))%T.
  Proof.
    typecheck.
  Qed.

  Hint Resolve EncodeUInt64_t EncodeUInt32_t DecodeUInt64_t DecodeUInt32_t : types.

  Definition UInt64Put: val :=
    λ: "p" "n",
    EncodeUInt64 "n" (slice.ptr "p").

  Theorem UInt64Put_t : ⊢ UInt64Put : (slice.T byteT -> uint64T -> unitT).
  Proof.
    typecheck.
  Qed.

  Definition UInt64Get: val :=
    λ: "p",
    DecodeUInt64 (slice.ptr "p").

  Theorem UInt64Get_t : ⊢ UInt64Get : (slice.T byteT -> uint64T).
  Proof.
    typecheck.
  Qed.

  Definition UInt32Put: val :=
    λ: "p" "n",
    EncodeUInt32 "n" (slice.ptr "p").

  Theorem UInt32Put_t : ⊢ UInt32Put : (slice.T byteT -> uint32T -> unitT).
  Proof.
    typecheck.
  Qed.

  Definition UInt32Get: val :=
    λ: "p",
    DecodeUInt32 (slice.ptr "p").

  Theorem UInt32Get_t : ⊢ UInt32Get : (slice.T byteT -> uint32T).
  Proof.
    typecheck.
  Qed.

End goose_lang.

Hint Resolve
     UInt64Put_t UInt64Get_t
     UInt32Put_t UInt32Get_t : types.
