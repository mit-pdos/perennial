From Perennial.goose_lang Require Export lang notation.
From Perennial.goose_lang Require Import struct typing.

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

Section goose_lang.
  Context `{ffi_sem: ext_semantics}.
  Context {ext_ty:ext_types ext}.

  Implicit Types (t:ty).

  Set Default Proof Using "ext ext_ty".

  Definition Var' s : @expr ext := Var s.
  Local Coercion Var' : string >-> expr.

(** allocation with a type annotation *)
Definition ref_to (t:ty): val := λ: "v", Alloc "v".

Definition raw_slice (t: ty): val :=
  λ: "p" "sz", ("p", "sz").

Theorem raw_slice_t t : ⊢ raw_slice t : (arrayT t -> uint64T -> slice.T t).
Proof.
  typecheck.
Qed.

Definition NewSlice (t: ty): val :=
  λ: "sz",
  if: "sz" = #0 then (#null, #0)
  else let: "p" := AllocN "sz" (zero_val t) in
       ("p", "sz").

Theorem NewSlice_t t : ⊢ NewSlice t : (uint64T -> slice.T t).
Proof.
  typecheck.
Qed.

Definition SliceSingleton: val :=
  λ: "x",
  let: "p" := AllocN #1 "x" in
  ("p", #1).

Theorem SliceSingleton_t t : ⊢ SliceSingleton : (t -> slice.T t).
Proof.
  type_step.
  type_step.
  { instantiate (1 := arrayT t).
    typecheck. }
  typecheck.
Qed.

(*
Definition MemCpy t: val :=
  λ: "dst" "src" (annot "n" uint64T),
    for-range: "i" < "n" :=
      ("dst" +ₗ "i") <-[t] ![t]("src" +ₗ "i").
*)

(* explicitly recursive version of MemCpy *)
Definition MemCpy_rec t: val :=
  rec: "memcpy" "dst" "src" "n" :=
    if: "n" = #0
    then #()
    else store_ty t "dst" (load_ty t "src");;
         "memcpy" ("dst" +ₗ[t] #1) ("src" +ₗ[t] #1) ("n" - #1).

Theorem MemCpy_rec_t t : ⊢ MemCpy_rec t : (arrayT t -> arrayT t -> uint64T -> unitT).
Proof.
Admitted.

Definition SliceCopy t : val :=
  λ: "dst" "src",
  let: "n" :=
     (if: slice.len "dst" ≤ slice.len "src"
     then slice.len "dst" else slice.len "src") in (* take the minimum *)
  MemCpy_rec t (slice.ptr "dst") (slice.ptr "src");;
  "n".

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
Definition SliceSkip t: val :=
  λ: "s" "n", (slice.ptr "s" +ₗ[t] "n", slice.len "s" - "n").

Theorem SliceSkip_t t : ⊢ SliceSkip t : (slice.T t -> uint64T -> slice.T t).
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

Definition SliceSubslice t: val :=
  λ: "s" "n1" "n2",
  if: "n2" < "n1"
  then Panic "slice indices out of order"
  else if: slice.len "s" ≤ "n2" - "n1"
       then Panic "slice index out-of-bounds"
       else (slice.ptr "s" +ₗ[t] "n1", "n2" - "n1").

Theorem SliceSubslice_t t : ⊢ SliceSubslice t : (slice.T t -> uint64T -> uint64T -> slice.T t).
Proof.
  typecheck.
Qed.

Definition SliceGet t: val :=
  λ: "s" "i",
  load_ty t (slice.ptr "s" +ₗ[t] "i").

(*
Theorem SliceGet_t t : ⊢ SliceGet t : (slice.T t -> uint64T -> t).
Proof.
  typecheck.
Qed.
*)

Definition SliceSet t: val :=
  λ: "s" "i" "v",
  store_ty t (slice.ptr "s" +ₗ[t] "i") "v".

(*
Theorem SliceSet_t t : ⊢ SliceSet t : (slice.T t -> uint64T -> t -> unitT).
Proof.
  type_step.
  type_step.
  type_step.
  eapply store_array_hasTy.
  { typecheck. }
  typecheck.
Qed.
*)

Definition SliceAppend t: val :=
  λ: "s1" "x",
  let: "p" := AllocN (slice.len "s1" + #1) (zero_val t) in
  MemCpy_rec t "p" (slice.ptr "s1") (slice.len "s1");;
  store_ty t ("p" +ₗ[t] slice.len "s1") "x";;
  (* TODO: unsound, need to de-allocate s1.p *)
  ("p", slice.len "s1" + #1).

Theorem SliceAppend_t t : ⊢ SliceAppend t : (slice.T t -> t -> slice.T t).
Proof.
Admitted.

Definition SliceAppendSlice t: val :=
  λ: "s1" "s2",
  let: "new_sz" := slice.len "s1" + slice.len "s2" in
  let: "p" := AllocN "new_sz" (zero_val t) in
  MemCpy_rec t "p" (slice.ptr "s1") (slice.len "s1");;
  MemCpy_rec t ("p" +ₗ slice.len "s2") (slice.ptr "s2") "new_sz";;
  (* TODO: unsound, need to de-allocate s1.p *)
  ("p", "new_sz").

Theorem SliceAppendSlice_t t : ⊢ SliceAppendSlice t : (slice.T t -> slice.T t -> slice.T t).
Proof.
Admitted.

Definition zero_array (t:ty): val :=
  λ: "sz", AllocN "sz" (zero_val t).

Definition ArrayCopy (t:ty): val :=
  λ: "sz" "a",
  let: "p" := zero_array t "sz" in
  MemCpy_rec t "p" "a" "sz";;
  "p".

Theorem zero_array_t t Γ : Γ ⊢ zero_array t : (uint64T -> arrayT t).
Proof.
  typecheck.
Qed.

Hint Resolve zero_array_t MemCpy_rec_t : types.

(*
Theorem ArrayCopy_t t Γ : Γ ⊢ ArrayCopy t : (uint64T -> arrayT t -> arrayT t).
Proof.
  typecheck.
Qed.
*)

Definition forSlice t: val :=
  λ: "body" "s",
  let: "len" := slice.len "s" in
  (rec: "loop" "i" :=
       if: ("i" < "len") then
         let: "x" := SliceGet t "s" "i" in
         "body" "i" "x";;
         "loop" ("i" + #1)
       else #()) #0.

(* TODO: this is super subtle to use, do we really need it? *)
Definition ForSlice t (iv: binder) (xv: binder) (s: expr) (body: expr): expr :=
  forSlice t (λ: iv xv, body)%E s.

End goose_lang.

Global Opaque slice.T raw_slice SliceAppend SliceAppendSlice.

Hint Resolve raw_slice_t NewSlice_t
     SliceTake_t SliceSkip_t SliceSubslice_t (* SliceGet_t SliceSet_t *)
     SliceAppend_t SliceAppendSlice_t : types.
Hint Resolve zero_array_t (* ArrayCopy_t *) : types.
