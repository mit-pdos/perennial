From Perennial.go_lang Require Export lang notation.
From Perennial.go_lang Require Import struct typing.

(** * Slice library

    Intended to model Go slices. We don't track slice capacity because our model
    soundly approximates slices as never having extra capacity.
 *)

Open Scope heap_types.

Module slice.
  Definition S t := mkStruct ["p" :: refT t; "len" :: intT].
  Definition T t : ty := refT t * intT.
  Section fields.
    Context `{ext_ty:ext_types}.

    Definition ptr: val := λ: "s", Fst (Var "s").
    Definition len: val := λ: "s", Snd (Var "s").

    Theorem ptr_t t : ⊢ ptr : (T t -> refT t).
    Proof.
      typecheck.
    Qed.
    Theorem len_t t : ⊢ len : (T t -> intT).
    Proof.
      typecheck.
    Qed.
  End fields.

  Definition nil {ext:ext_op} : val := (#null, #0).
  Theorem nil_t `{ext_ty:ext_types} t : ⊢ nil : T t.
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

Theorem NewSlice_t t : ⊢ NewSlice t : (intT -> slice.T t).
Proof.
  typecheck.
Qed.

Definition MemCpy: val :=
  λ: "dst" "src" (annot "n" intT),
    for-range: "i" < "n" :=
      ("dst" +ₗ "i") <- !("src" +ₗ "i").

Theorem MemCpy_t t : ⊢ MemCpy : (refT t -> refT t -> intT -> unitT).
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

Theorem MemCpy_rec_t t : ⊢ MemCpy_rec : (refT t -> refT t -> intT -> unitT).
Proof.
  typecheck.
Qed.

Definition SliceSkip: val :=
  λ: "s" "n", (slice.ptr "s" +ₗ "n", slice.len "s" - "n").

Theorem SliceSkip_t t : ⊢ SliceSkip : (slice.T t -> intT -> slice.T t).
Proof.
  typecheck.
Qed.

Definition SliceTake: val :=
  λ: "s" "n", if: slice.len "s" ≤ "n"
              then Panic "slice index out-of-bounds"
              else (slice.ptr "s", "n").

Theorem SliceTake_t t : ⊢ SliceTake : (slice.T t -> intT -> slice.T t).
Proof.
  typecheck.
Qed.

Definition SliceSubslice: val :=
  λ: "s" "n1" "n2",
  if: slice.len "s" ≤ "n2" - "n1"
  then Panic "slice index out-of-bounds"
  else (slice.ptr "s" +ₗ "n1", "n2" - "n1").

Theorem SliceSubslice_t t : ⊢ SliceSubslice : (slice.T t -> intT -> intT -> slice.T t).
Proof.
  typecheck.
Qed.

Definition SliceGet: val :=
  λ: "s" "i",
  !(slice.ptr "s" +ₗ "i").

Theorem SliceGet_t t : ⊢ SliceGet : (slice.T t -> intT -> t).
Proof.
  typecheck.
Qed.

Definition SliceSet: val :=
  λ: "s" "i" "v",
  (slice.ptr "s" +ₗ "i") <- "v".

Theorem SliceSet_t t : ⊢ SliceSet : (slice.T t -> intT -> t -> unitT).
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

Theorem UInt64Put_t : ⊢ UInt64Put : (intT -> slice.T byteT -> unitT).
Proof.
  typecheck.
Qed.

Definition UInt64Get: val :=
  λ: "p",
  DecodeInt (slice.ptr "p").

Theorem UInt64Get_t : ⊢ UInt64Get : (slice.T byteT -> intT).
Proof.
  typecheck.
Qed.

End go_lang.

Hint Resolve NewSlice_t
     SliceTake_t SliceSkip_t SliceSubslice_t SliceGet_t SliceSet_t
     UInt64Put_t UInt64Get_t : types.
