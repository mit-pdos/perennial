From iris.proofmode Require Import tactics.
From Perennial.go_lang Require Import lang notation.
From Perennial.go_lang Require Import struct typing slice.
From Perennial.go_lang Require Import lifting array.
From Perennial.go_lang Require Import proofmode tactics notation map.

Section go_lang.
  Context `{ffi_sem: ext_semantics}.
  Context {ext_ty:ext_types ext}.

  Context `{!ffi_interp ffi}.
  Context `{!heapG Σ}.

  Set Default Proof Using "ext ext_ty".

  Definition Var' s : @expr ext := Var s.
  Local Coercion Var' : string >-> expr.

  Definition EncodeUInt32: val :=
    λ: "n" "p",
    "p" +ₗ #0 <- to_u8 ("n" ≫ #(U32 $ 0*8));;
    "p" +ₗ #1 <- to_u8 ("n" ≫ #(U32 $ 1*8));;
    "p" +ₗ #2 <- to_u8 ("n" ≫ #(U32 $ 2*8));;
    "p" +ₗ #3 <- to_u8 ("n" ≫ #(U32 $ 3*8)).

  Theorem EncodeUInt32_t : (⊢ EncodeUInt32 : (uint32T -> arrayT byteT -> unitT))%T.
  Proof.
    typecheck.
  Qed.

  Definition DecodeUInt32: val :=
    λ: "p",
    to_u32 (!("p" +ₗ #0)) ≪ #(U32 $ 0*8) ∥
    to_u32 (!("p" +ₗ #1)) ≪ #(U32 $ 1*8) ∥
    to_u32 (!("p" +ₗ #2)) ≪ #(U32 $ 2*8) ∥
    to_u32 (!("p" +ₗ #3)) ≪ #(U32 $ 3*8)
  .

  Theorem DecodeUInt32_t : (⊢ DecodeUInt32 : (arrayT byteT -> uint32T))%T.
  Proof.
    typecheck.
  Qed.

  Lemma word_sru_0 width (word: Interface.word width) (ok: word.ok word)
        (x: word) s : int.val s = 0 -> word.sru x s = x.
  Proof.
    intros.
    apply Properties.word.unsigned_inj.
    rewrite word.unsigned_sru.
    - rewrite H.
      rewrite Z.shiftr_0_r.
      unfold word.wrap.
      rewrite Properties.word.wrap_unsigned.
      auto.
    - rewrite H.
      apply word.width_pos.
  Qed.

  Opaque word.sru.

  Theorem wp_EncodeUInt32 (l: loc) (x: u32) vs s E :
    {{{ l ↦∗ vs }}}
      EncodeUInt32 #x #l @ s ; E
    {{{ RET #(); l ↦∗ ((λ (b: byte), #b) <$> u32_le x) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    unfold EncodeUInt32.
    wp_lam.
    wp_let.
    wp_pures.
    rewrite Zmod_0_l.
    rewrite loc_add_0.
    change (0 * 8) with 0.
    rewrite word_sru_0; [ | simpl; rewrite Zmod_0_l; auto ].
  Abort.

  Definition EncodeUInt64: val :=
    λ: "n" "p",
    "p" +ₗ #0 <- to_u8 ("n" ≫ #(0*8));;
    "p" +ₗ #1 <- to_u8 ("n" ≫ #(1*8));;
    "p" +ₗ #2 <- to_u8 ("n" ≫ #(2*8));;
    "p" +ₗ #3 <- to_u8 ("n" ≫ #(3*8));;
    "p" +ₗ #4 <- to_u8 ("n" ≫ #(4*8));;
    "p" +ₗ #5 <- to_u8 ("n" ≫ #(5*8));;
    "p" +ₗ #6 <- to_u8 ("n" ≫ #(6*8));;
    "p" +ₗ #7 <- to_u8 ("n" ≫ #(7*8))
  .

  Theorem EncodeUInt64_t : (⊢ EncodeUInt64 : (uint64T -> arrayT byteT -> unitT))%T.
  Proof.
    typecheck.
  Qed.

  Definition DecodeUInt64: val :=
    λ: "p",
    to_u64 (!("p" +ₗ #0)) ≪ #(U64 $ 0*8) ∥
    to_u64 (!("p" +ₗ #1)) ≪ #(U64 $ 1*8) ∥
    to_u64 (!("p" +ₗ #2)) ≪ #(U64 $ 2*8) ∥
    to_u64 (!("p" +ₗ #3)) ≪ #(U64 $ 3*8) ∥
    to_u64 (!("p" +ₗ #4)) ≪ #(U64 $ 4*8) ∥
    to_u64 (!("p" +ₗ #5)) ≪ #(U64 $ 5*8) ∥
    to_u64 (!("p" +ₗ #6)) ≪ #(U64 $ 6*8) ∥
    to_u64 (!("p" +ₗ #7)) ≪ #(U64 $ 7*8)
  .

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

End go_lang.

Hint Resolve
     UInt64Put_t UInt64Get_t
     UInt32Put_t UInt32Get_t : types.
