From Perennial.goose_lang.lib Require Import typed_mem.impl.
From Perennial.goose_lang.lib Require Import control.impl.

(** * Slice library *)

Open Scope heap_types.

Module slice.
  Section types.
    Context `{ext_ty: ext_types}.
    Definition T t : ty := (arrayT t * uint64T * uint64T)%ht.

    Definition ptr: val := λ: "s", Fst (Fst (Var "s")).
    Definition len: val := λ: "s", Snd (Fst (Var "s")).
    Definition cap: val := λ: "s", Snd (Var "s").

    Theorem ptr_t t : ∅ ⊢ ptr : (T t -> arrayT t).
    Proof.
      typecheck.
    Qed.
    Theorem len_t t : ∅ ⊢ len : (T t -> uint64T).
    Proof.
      typecheck.
    Qed.

    Definition nil : val := (#null, #0, #0).
    Theorem nil_t t : ∅ ⊢ nil : T t.
    Proof.
      typecheck.
    Qed.
  End types.
End slice.

Hint Resolve slice.ptr_t slice.len_t slice.nil_t : types.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context {ext_ty:ext_types ext}.

Implicit Types (t:ty).

Set Default Proof Using "ext ext_ty".

Local Coercion Var' s: expr := Var s.

Theorem has_zero_slice_T t : has_zero (slice.T t).
Proof.
  auto.
Qed.

Definition raw_slice (t: ty): val :=
  λ: "p" "sz",
  ("p", "sz", "sz").

Theorem raw_slice_t t : ∅ ⊢ raw_slice t : (arrayT t -> uint64T -> slice.T t).
Proof.
  typecheck.
Qed.

Definition make_cap: val :=
  λ: "sz",
  let: "extra" := ArbitraryInt in
  (* check for overflow *)
  if: "sz" + "extra" > "sz"
  then "sz" + "extra" else "sz".

Definition NewSlice (t: ty): val :=
  rec: "NewSlice" "sz" :=
  if: "sz" = #0 then slice.nil
  else let: "cap" := make_cap "sz" in
       let: "p" := AllocN "cap" (zero_val t) in
       (Var "p", Var "sz", Var "cap").

Definition SliceSingleton: val :=
  λ: "x",
  let: "p" := AllocN #1 "x" in
  ("p", #1, #1).

Definition MemCpy_rec t: val :=
  rec: "memcpy" "dst" "src" "n" :=
    if: "n" = #0
    then #()
    else "dst" <-[t] (![t] "src");;
         "memcpy" ("dst" +ₗ[t] #1) ("src" +ₗ[t] #1) ("n" - #1).

Definition SliceCopy t : val :=
  λ: "dst" "src",
  let: "n" :=
     (if: slice.len "dst" < slice.len "src"
     then slice.len "dst" else slice.len "src") in (* take the minimum *)
  MemCpy_rec t (slice.ptr "dst") (slice.ptr "src") "n";;
  "n".

(* this models &s[i] (which looks a little like a get but is very different) *)
Definition SliceRef: val :=
  λ: "s" "i", if: "i" < slice.len "s"
              then (slice.ptr "s" +ₗ "i")
              else Panic "slice index out-of-bounds".

(* TODO: it would be nice if we could panic in the model if this goes
out-of-bounds, but it seems we need to unfold the definition to use it *)
Definition SliceSkip t: val :=
  λ: "s" "n", (slice.ptr "s" +ₗ[t] "n", slice.len "s" - "n", slice.cap "s" - "n").

Definition SliceTake: val :=
  λ: "s" "n", if: slice.len "s" < "n"
              then Panic "slice index out-of-bounds"
              else
                (slice.ptr "s", "n", slice.cap "s").

Definition SliceSubslice t: val :=
  λ: "s" "n1" "n2",
  if: "n2" < "n1"
  then Panic "slice indices out of order"
  else if: slice.len "s" < "n2" - "n1"
       then Panic "slice index out-of-bounds"
       else (slice.ptr "s" +ₗ[t] "n1", "n2" - "n1", "n2" - "n1").

Theorem SliceSubslice_t t : ∅ ⊢ SliceSubslice t : (slice.T t -> uint64T -> uint64T -> slice.T t).
Proof.
  typecheck.
Qed.

Definition SliceGet t: val :=
  λ: "s" "i",
  load_ty t (slice.ptr "s" +ₗ[t] "i").

Definition SliceSet t: val :=
  λ: "s" "i" "v",
  (slice.ptr "s" +ₗ[t] "i") <-[t] "v".

Definition SliceAppend t: val :=
  λ: "s1" "x",
  Assume (slice.len "s1" < #(2^64-1));;
  let: "sz" := slice.len "s1" + #1 in
  if: slice.cap "s1" - slice.len "s1" ≥ #1 then
    (* re-use existing capacity *)
    let: "p" := slice.ptr "s1" in
    ("p" +ₗ[t] slice.len "s1") <-[t] "x";;
    ("p", "sz", slice.cap "s1")
  else
    (* non-deterministically grow and copy *)
    let: "cap" := make_cap "sz" in
    let: "p" := AllocN "cap" (zero_val t) in
    MemCpy_rec t "p" (slice.ptr "s1") (slice.len "s1");;
    ("p" +ₗ[t] slice.len "s1") <-[t] "x";;
    ("p", "sz", "cap").

(* TODO: update to handle capacity correctly *)
Definition SliceAppendSlice t: val :=
  λ: "s1" "s2",
  let: "new_sz" := slice.len "s1" + slice.len "s2" in
  let: "p" := AllocN "new_sz" (zero_val t) in
  MemCpy_rec t "p" (slice.ptr "s1") (slice.len "s1");;
  MemCpy_rec t ("p" +ₗ slice.len "s2") (slice.ptr "s2") "new_sz";;
  (* TODO: unsound, need to de-allocate s1.p *)
  ("p", "new_sz").

Definition ArrayCopy (t:ty): val :=
  λ: "sz" "a",
  let: "p" := AllocN "sz" (zero_val t) in
  MemCpy_rec t "p" "a" "sz";;
  "p".

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

Hint Resolve has_zero_slice_T : core.
Global Opaque slice.T raw_slice SliceAppend SliceAppendSlice.
