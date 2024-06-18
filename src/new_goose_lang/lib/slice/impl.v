From Perennial.goose_lang Require Import notation.
From Perennial.new_goose_lang.lib Require Import mem.impl.
From Perennial.goose_lang.lib Require Import control.impl.

(** * Slice library *)

Module slice.
  Section types.
    Context `{ffi_syntax}.

    Definition ptr: val := λ: "s", Fst (Fst (Var "s")).
    Definition len: val := λ: "s", Snd (Fst (Var "s")).
    Definition cap: val := λ: "s", Snd (Var "s").

  End types.
End slice.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.

Implicit Types (t : go_type).

Set Default Proof Using "ext ext_ty".

Local Coercion Var' s: expr := Var s.

Definition raw_slice (t : go_type): val :=
  λ: "p" "sz",
  ("p", "sz", "sz").

Definition make_cap: val :=
  λ: "sz",
  let: "extra" := ArbitraryInt in
  (* check for overflow *)
  if: "sz" + "extra" > "sz"
  then "sz" + "extra" else "sz".

Definition NewSlice t : val :=
  λ: "sz",
  if: "sz" = #0 then nil
  else let: "cap" := make_cap "sz" in
       let: "p" := AllocN "cap" (zero_val t) in
       (Var "p", Var "sz", Var "cap").

Definition NewSliceWithCap t : val :=
  λ: "sz" "cap",
  if: "cap" < "sz" then Panic "NewSlice with cap smaller than len"
  else if: "cap" = #0 then nil
  else let: "p" := AllocN "cap" (zero_val t) in
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
         "memcpy" (BinOp (OffsetOp (go_type_size t)) "dst" #1)
                  (BinOp (OffsetOp (go_type_size t)) "src" #1)
                  ("n" - #1).

Definition SliceCopy t : val :=
  λ: "dst" "src",
  let: "n" :=
     (if: slice.len "dst" < slice.len "src"
     then slice.len "dst" else slice.len "src") in (* take the minimum *)
  MemCpy_rec t (slice.ptr "dst") (slice.ptr "src") "n";;
  "n".

(* this models &s[i] (which looks a little like a get but is very different) *)
Definition SliceRef t: val :=
  λ: "s" "i", if: "i" < slice.len "s"
              then (slice.ptr "s" +ₗ[t] "i")
              else Panic "slice index out-of-bounds".

(* TODO: it would be nice if we could panic in the model if this goes
out-of-bounds, but it seems we need to unfold the definition to use it *)
Definition SliceSkip t: val :=
  λ: "s" "n", (slice.ptr "s" +ₗ[t] "n", slice.len "s" - "n", slice.cap "s" - "n").

Definition SliceTake: val :=
  λ: "s" "n", if: slice.cap "s" < "n"
              then Panic "slice (take) index out-of-bounds"
              else
                (slice.ptr "s", "n", slice.cap "s").

Definition SliceSubslice t: val :=
  λ: "s" "n1" "n2",
  if: "n2" < "n1"
  then Panic "slice indices out of order"
  else if: slice.cap "s" < "n2"
       then Panic "slice (subslice) index out-of-bounds"
       else (slice.ptr "s" +ₗ[t] "n1", "n2" - "n1", slice.cap "s" - "n1").

Definition SliceGet t: val :=
  λ: "s" "i",
  ![t] (slice.ptr "s" +ₗ[t] "i").

Definition SliceSet t: val :=
  λ: "s" "i" "v",
  (slice.ptr "s" +ₗ[t] "i") <-[t] "v".

Definition ArrayCopy t : val :=
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

(* FIXME: *)
(*
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

Definition SliceAppendSlice t: val :=
  λ: "s1" "s2",
  let: "s" := ref_to (slice.T t) "s1" in
  ForSlice t <> "x" "s2"
    ("s" <-[slice.T t] (SliceAppend t (![slice.T t] "s") "x"));;
  ![slice.T t] "s". *)

End goose_lang.

(* #[global]
Hint Resolve has_zero_slice_T : core. *)
Global Opaque raw_slice (* SliceAppend SliceAppendSlice *).
