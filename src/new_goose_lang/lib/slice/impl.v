From Perennial.goose_lang Require Import notation.
From Perennial.new_goose_lang.lib Require Import mem.impl loop.impl.
From Perennial.goose_lang.lib Require Import control.impl.

Module slice.
(* FIXME: seal these functions *)
Section goose_lang.
Context `{ffi_syntax}.

Local Coercion Var' s: expr := Var s.
Definition nil : val := slice_nil.
Definition ptr : val := λ: "s", Fst (Fst "s").
Definition len : val := λ: "s", Snd (Fst "s").
Definition cap : val := λ: "s", Snd "s".

(* XXX: this computes a nondeterministic unallocated address by using
   "(Loc 1 0) +ₗ ArbiraryInt"*)
Definition make3 t : val :=
  λ: "sz" "cap",
  if: "cap" < "sz" then Panic "NewSlice with cap smaller than len"
  else if: "cap" = #0 then (#(Loc 1 0) +ₗ ArbitraryInt, Var "sz", Var "cap")
  else let: "p" := AllocN "cap" (zero_val t) in
       (Var "p", Var "sz", Var "cap").

Definition make2 t : val :=
  λ: "sz", make3 t "sz" "sz".

Definition copy t : val :=
  λ: "dst" "src",
  (* take the minimum *)
  let: "n" := (if: len "dst" < len "src" then len "dst" else len "src") in
  (rec: "copy_aux" "dst" "src" "n" :=
    if: "n" = #0
    then #()
    else "dst" <-[t] (![t] "src");;
         "copy_aux" (BinOp (OffsetOp (go_type_size t)) "dst" #1)
                  (BinOp (OffsetOp (go_type_size t)) "src" #1)
                  ("n" - #1)) "n".

(* computes `&s[i]` *)
Definition elem_ref t : val :=
  λ: "s" "i", if: "i" < len "s"
              then (Fst (Fst "s") +ₗ[t] "i")
              else Panic "slice index out-of-bounds".

(* TODO: function that takes an array/list as input to construct a slice with multiple elements *)

Definition slice t : val :=
  λ: "a" "low" "high",
  if: (#0 ≤ "low") && ("low" < "high") && ("high" < len "a") then
    ((Fst $ Fst "s") +ₗ[t] "low", "high" - "low", cap "s" - "low")
  else Panic "slice indices out of order"
.

Definition for_range t : val :=
  λ: "s" "body",
  let: "i" := ref_ty uint64T (zero_val uint64T) in
  for: ("i" < len "s") ; Skip :=
    "body" "i" (![t] (elem_ref t "s"))
.

Definition copy t : val :=
  λ: "s" "x",
  let: "s" := ref_to (slice.T t) "s1" in
  for_range t <> "x" "s2"
    ("s" <-[slice.T t] (SliceAppend t (![slice.T t] "s") "x"));;
  ![slice.T t] "s".

Definition append t : val :=
  λ: "s" "x",
  let: "s" := ref_to (slice.T t) "s1" in
  for_range t <> "x" "s2"
    ("s" <-[slice.T t] (SliceAppend t (![slice.T t] "s") "x"));;
  ![slice.T t] "s".

End goose_lang.
End slice.
