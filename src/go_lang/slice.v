From Perennial.go_lang Require Export lang notation.
From Perennial.go_lang Require Import struct typing.

(** * Slice library

    Intended to model Go slices. We don't track slice capacity because our model
    soundly approximates slices as never having extra capacity.
 *)

Open Scope heap_types.

Module slice.
  Section types.
    Context `{ext_ty: ext_types}.
    Definition S t := mkStruct ["p" :: refT t; "len" :: uint64T].
    Definition T t : ty := arrayT t * uint64T.

    Definition ptr: val := λ: "s", Fst (Var "s").
    Definition len: val := λ: "s", Snd (Var "s").

    Theorem ptr_t t : ⊢ ptr : (T t -> arrayT t).
    Proof.
      typecheck.
    Qed.
    Theorem len_t t : ⊢ len : (T t -> uint64T).
    Proof.
      typecheck.
    Qed.

    Definition nil : val := (#null, #0).
    Theorem nil_t t : ⊢ nil : T t.
    Proof.
      typecheck.
    Qed.
  End types.
End slice.

Hint Resolve slice.ptr_t slice.len_t slice.nil_t : types.

Section go_lang.
  Context `{ffi_sem: ext_semantics}.
  Context {ext_ty:ext_types ext}.

  Set Default Proof Using "ext ext_ty".

  Definition Var' s : @expr ext := Var s.
  Local Coercion Var' : string >-> expr.

Definition raw_slice (t: ty): val :=
  λ: "p" "sz", ("p", "sz").

Theorem raw_slice_t t : ⊢ raw_slice t : (arrayT t -> uint64T -> slice.T t).
Proof.
  typecheck.
Qed.

Definition NewSlice (t: ty): val :=
  λ: "sz",
  let: "p" := AllocN "sz" (zero_val t) in
  ("p", "sz").

Theorem NewSlice_t t : ⊢ NewSlice t : (uint64T -> slice.T t).
Proof.
  typecheck.
Qed.

Definition MemCpy: val :=
  λ: "dst" "src" (annot "n" uint64T),
    for-range: "i" < "n" :=
      ("dst" +ₗ "i") <- !("src" +ₗ "i").

Theorem MemCpy_t t : ⊢ MemCpy : (arrayT t -> arrayT t -> uint64T -> unitT).
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

Theorem MemCpy_rec_t t : ⊢ MemCpy_rec : (arrayT t -> arrayT t -> uint64T -> unitT).
Proof.
  typecheck.
Qed.

(* this models &s[i] (which looks a little like a get but is very different) *)
Definition SliceRef: val :=
  λ: "s" "i", if: "i" < slice.len "s"
              then (slice.ptr "s" +ₗ "i")
              else Panic "slice index out-of-bounds".

Theorem SliceRef_t t : ⊢ SliceRef : (slice.T t -> uint64T -> arrayT t).
Proof.
  typecheck.
Qed.

(* TODO: it would be nice if we could panic in the model if this goes
out-of-bounds, but it seems we need to unfold the definition to use it *)
Definition SliceSkip: val :=
  λ: "s" "n", (slice.ptr "s" +ₗ "n", slice.len "s" - "n").

Theorem SliceSkip_t t : ⊢ SliceSkip : (slice.T t -> uint64T -> slice.T t).
Proof.
  typecheck.
Qed.

Definition SliceTake: val :=
  λ: "s" "n", if: slice.len "s" ≤ "n"
              then Panic "slice index out-of-bounds"
              else (slice.ptr "s", "n").

Theorem SliceTake_t t : ⊢ SliceTake : (slice.T t -> uint64T -> slice.T t).
Proof.
  typecheck.
Qed.

Definition SliceSubslice: val :=
  λ: "s" "n1" "n2",
  if: slice.len "s" ≤ "n2" - "n1"
  then Panic "slice index out-of-bounds"
  else (slice.ptr "s" +ₗ "n1", "n2" - "n1").

Theorem SliceSubslice_t t : ⊢ SliceSubslice : (slice.T t -> uint64T -> uint64T -> slice.T t).
Proof.
  typecheck.
Qed.

Definition SliceGet: val :=
  λ: "s" "i",
  !(slice.ptr "s" +ₗ "i").

Theorem SliceGet_t t : ⊢ SliceGet : (slice.T t -> uint64T -> t).
Proof.
  typecheck.
Qed.

Definition SliceSet: val :=
  λ: "s" "i" "v",
  (slice.ptr "s" +ₗ "i") <- "v".

Theorem SliceSet_t t : ⊢ SliceSet : (slice.T t -> uint64T -> t -> unitT).
Proof.
  type_step.
  type_step.
  type_step.
  eapply store_array_hasTy.
  { typecheck. }
  typecheck.
Qed.

Definition SliceAppend: val :=
  λ: "s1" "x",
  let: "p" := AllocN (slice.len "s1" + #1) #() in
  MemCpy_rec "p" (slice.ptr "s1") (slice.len "s1");;
  ("p" +ₗ slice.len "s1") <- "x";;
  (* TODO: unsound, need to de-allocate s1.p *)
  ("p", slice.len "s1" + #1).

(* TODO: doesn't work since initial value is of wrong type *)
Theorem SliceAppend_t t : ⊢ SliceAppend : (slice.T t -> t -> slice.T t).
Proof.
Admitted.

Definition SliceAppendSlice: val :=
  λ: "s1" "s2",
  let: "new_sz" := slice.len "s1" + slice.len "s2" in
  let: "p" := AllocN "new_sz" #() in
  MemCpy "p" (slice.ptr "s1") (slice.len "s1");;
  MemCpy ("p" +ₗ slice.len "s2") (slice.ptr "s2") "new_sz";;
  (* TODO: unsound, need to de-allocate s1.p *)
  ("p", "new_sz").

(* TODO: doesn't work since initial value is of wrong type *)
Theorem SliceAppendSlice_t t : ⊢ SliceAppendSlice : (slice.T t -> slice.T t -> slice.T t).
Proof.
Admitted.

Definition zero_array (t:ty): val :=
  λ: "sz", AllocN "sz" (zero_val t).

Definition ArrayCopy (t:ty): val :=
  λ: "sz" "a",
  let: "p" := zero_array t "sz" in
  MemCpy "p" "a" "sz";;
  "p".

Theorem zero_array_t t Γ : Γ ⊢ zero_array t : (uint64T -> arrayT t).
Proof.
  typecheck.
Qed.

Hint Resolve zero_array_t MemCpy_t : types.

Theorem ArrayCopy_t t Γ : Γ ⊢ ArrayCopy t : (uint64T -> arrayT t -> arrayT t).
Proof.
  typecheck.
Qed.

(* TODO: this is now an ordinary program and doesn't need these __ variables *)
Definition forSlice: val :=
  λ: "__body" "__s",
  let: "__len" := slice.len "__s" in
  (rec: "__loop" "__i" :=
       if: ("__i" < "__len") then
         let: "__x" := SliceGet "__s" "__i" in
         "__body" "__i" "__x";;
         "__loop" ("__i" + #1)
       else #()) #0.

Definition ForSlice (iv: string) (xv: string) (s: expr) (body: expr): expr :=
  forSlice (λ: iv xv, body)%E s.

End go_lang.

Global Opaque slice.T raw_slice SliceAppend SliceAppendSlice.

Hint Resolve raw_slice_t NewSlice_t
     SliceTake_t SliceSkip_t SliceSubslice_t SliceGet_t SliceSet_t
     SliceAppend_t SliceAppendSlice_t : types.
Hint Resolve zero_array_t ArrayCopy_t : types.
