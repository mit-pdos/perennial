From Perennial.go_lang Require Export lang notation.
From Perennial.go_lang Require Import struct typing.

(** * Slice library

    Intended to model Go slices. We don't track slice capacity because our model
    soundly approximates slices as never having extra capacity.
 *)

Open Scope heap_types.

Module slice.
  Definition sliceS := mkStruct ["p"; "len"].
  Definition T t : ty := refT t * intT.
  Section fields.
    Context `{ext_ty:ext_types}.

    Definition ptr := structF! sliceS "p".
    Definition len: val := structF! sliceS "len".
    Theorem ptr_t t Γ : Γ ⊢ ptr : (T t -> refT t).
    Proof.
      typecheck.
    Qed.
    Theorem len_t t Γ : Γ ⊢ len : (T t -> intT).
    Proof.
      typecheck.
    Qed.
  End fields.

  Definition nil {ext:ext_op} : val := (#null, #0).
  Theorem nil_t `{ext_ty:ext_types} Γ t : Γ ⊢ nil : T t.
  Proof.
    typecheck.
  Qed.
End slice.

Hint Resolve slice.ptr_t slice.len_t slice.nil_t : types.

Section go_lang.
  Context `{ffi_sem: ext_semantics}.
  Context {ext_ty:ext_types ext}.

  Definition Var' s : @expr ext := Var s.
  Local Coercion Var' : string >-> expr.

Definition NewSlice (t: ty): val :=
  λ: "sz",
  let: "p" := AllocN "sz" (zero_val t) in
  ("p", "sz").

Theorem NewSlice_t : `(Γ ⊢ NewSlice t : (intT -> slice.T t)).
Proof.
  typecheck.
Qed.

Definition MemCpy: val :=
  λ: "dst" "src" (annot "n" intT),
    for: "i" < "n" :=
    ("dst" +ₗ "i") <- !("src" +ₗ "i").

Theorem MemCpy_t Γ t : Γ ⊢ MemCpy : (refT t -> refT t -> intT -> unitT).
Proof.
  typecheck.
Qed.

(* explicitly recursive version of MemCpy *)
Definition MemCpy_rec: val :=
  rec: "memcpy" "dst" "src" "n" :=
    if: "n" = #0
    then #()
    else "dst" <- !"src";;
         "memcpy" ("dst" +ₗ #1) ("src" +ₗ #1) ("n" - #1).

Theorem MemCpy_rec_t Γ t : Γ ⊢ MemCpy_rec : (refT t -> refT t -> intT -> unitT).
Proof.
  typecheck.
Qed.

Definition SliceSkip: val :=
  λ: "s" "n", (slice.ptr "s" +ₗ "n", slice.len "s" - "n").

Theorem SliceSkip_t Γ t : Γ ⊢ SliceSkip : (slice.T t -> intT -> slice.T t).
Proof.
  typecheck.
Qed.

Definition SliceTake: val :=
  λ: "s" "n", if: slice.len "s" ≤ "n"
              then Panic "slice index out-of-bounds"
              else (slice.ptr "s", "n").

Theorem SliceTake_t Γ t : Γ ⊢ SliceTake : (slice.T t -> intT -> slice.T t).
Proof.
  typecheck.
Qed.

Definition SliceGet: val :=
  λ: "s" "i",
  !(slice.ptr "s" +ₗ "i").

Theorem SliceGet_t Γ t : Γ ⊢ SliceGet : (slice.T t -> intT -> t).
Proof.
  typecheck.
Qed.

Definition SliceSet: val :=
  λ: "s" "i" "v",
  (slice.ptr "s" +ₗ "i") <- "v".

Theorem SliceSet_t : `(Γ ⊢ SliceSet : (slice.T t -> intT -> t -> unitT)).
Proof.
  typecheck.
Qed.

Definition SliceAppend: val :=
  λ: "s1" "s2",
  let: "p" := AllocN (slice.len "s1" + slice.len "s2") #() in
  MemCpy "p" (slice.ptr "s1");;
  MemCpy ("p" +ₗ slice.len "s2") (slice.ptr "s2");;
  (* TODO: unsound, need to de-allocate s1.p *)
  ("p", slice.len "s1" + slice.len "s2").

(* doesn't work since initial value is of wrong type
Theorem SliceAppend_t Γ t : Γ ⊢ SliceAppend : (slice.T t -> slice.T t -> slice.T t).
Proof.
  typecheck.
Qed. *)

Definition UInt64Put: val :=
  λ: "n" "p",
  EncodeInt "n" (slice.ptr "p").

Theorem UInt64Put_t Γ : Γ ⊢ UInt64Put : (intT -> slice.T byteT -> unitT).
Proof.
  typecheck.
Qed.

Definition UInt64Get: val :=
  λ: "p",
  DecodeInt (slice.ptr "p").

Theorem UInt64Get_t Γ : Γ ⊢ UInt64Get : (slice.T byteT -> intT).
Proof.
  typecheck.
Qed.

End go_lang.

Hint Resolve NewSlice_t
     SliceTake_t SliceSkip_t SliceGet_t SliceSet_t
     UInt64Put_t UInt64Get_t : types.
