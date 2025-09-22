From New.golang.defn Require Import loop assume exception typing list mem builtin.
From Perennial Require Import base.

Module slice.
(* FIXME: seal these functions *)
Section goose_lang.
Context `{ffi_syntax}.

Definition ptr : val := λ: "s",
                          let: "s" := (match: "s" with InjL "s" => "s" | InjR <> => #() end) in
                          Fst (Fst "s").
Definition len : val := λ: "s",
                          let: "s" := (match: "s" with InjL "s" => "s" | InjR <> => #() end) in
                          Snd (Fst "s").
Definition cap : val := λ: "s",
                          let: "s" := (match: "s" with InjL "s" => "s" | InjR <> => #() end) in
                          Snd "s".

(* XXX: this computes a nondeterministic unallocated address by using
   "(Loc 1 0) +ₗ ArbiraryInt"*)
Definition make3 t : val :=
  λ: "sz" "cap",
  if: int_lt "cap" "sz" then Panic "NewSlice with cap smaller than len"
  else if: "cap" = #(W64 0) then InjL (#(Loc 1 0) +ₗ ArbitraryInt, Var "sz", Var "cap")
  else let: "p" := AllocN "cap" (zero_val t) in
       InjL ("p", "sz", "cap").

Definition make2 t : val :=
  λ: "sz", make3 t "sz" "sz".

(* computes `&s[i]` *)
Definition elem_ref (t : go_type) : val :=
  λ: "s" "i", if: int_lt "i" (len "s")
              then ((ptr "s") +ₗ[t] "i")
              else Panic "slice index out-of-bounds".

(* s[a:b], as well as s[a:] = s[a:len(s)] and s[:b] = s[0:b] *)
Definition slice t : val :=
  λ: "s" "low" "high",
  if: (int_leq #(W64 0) "low") && (int_leq "low" "high") && (int_leq "high" (cap "s")) then
    InjL ((ptr "s") +ₗ[t] "low", "high" - "low", cap "s" - "low")
  else Panic "slice indices out of order"
.

(* s[a:b:c] (picking a specific capacity c) *)
Definition full_slice t : val :=
  λ: "s" "low" "high" "max",
  if: (int_leq #(W64 0) "low") && (int_leq "low" "high") && (int_leq "high" "max") && (int_leq "max" (cap "s")) then
    InjL ((ptr "s") +ₗ[t] "low", "high" - "low", "max" - "low")
  else Panic "slice indices out of order"
.

Definition for_range t : val :=
  λ: "s" "body",
  let: "i" := mem.alloc int64T #() in
  for: (λ: <>, int_lt (![int64T] "i") (len "s")) ; (λ: <>, "i" <-[int64T] (![int64T] "i") + #(W64 1)) :=
    (λ: <>, "body" (![int64T] "i") (![t] (elem_ref t "s" (![int64T] "i"))))
.

Definition copy t : val :=
  λ: "dst" "src",
  let: "i" := mem.alloc int64T #() in
  (for: (λ: <>, int_lt (![int64T] "i") (len "dst") && (int_lt (![int64T] "i") (len "src"))) ; (λ: <>, Skip) :=
    (λ: <>,
    do: (let: "i_val" := ![int64T] "i" in
      elem_ref t "dst" "i_val" <-[t] ![t] (elem_ref t "src" "i_val");;
      "i" <-[int64T] "i_val" + #(W64 1))));;
  ![int64T] "i"
.

(* only for internal use, not an external model *)
Definition _new_cap : val :=
  λ: "len",
    let: "extra" := ArbitraryInt in
    if: int_leq "len" ("len" + "extra") then "len" + "extra"
    else "len".

Definition append t : val :=
  λ: "s" "x",
  let: "new_len" := sum_assume_no_overflow_signed (len "s") (len "x") in
  if: (cap "s") ≥ "new_len" then
    (* "grow" s to include its capacity *)
    let: "s_new" := slice t "s" #(W64 0) "new_len" in
    (* copy "x" past the original "s" *)
    copy t (slice t "s_new" (len "s") "new_len") "x";;
    "s_new"
  else
    let: "new_cap" := _new_cap "new_len" in
    let: "s_new" := make3 t "new_len" "new_cap" in
    copy t "s_new" "s" ;;
    copy t (slice t "s_new" (len "s") "new_len") "x" ;;
    "s_new".

(* Takes in a list as input, and turns it into a heap-allocated slice. *)
Definition literal t : val :=
  λ: "elems",
  let: "len" := list.Length "elems" in
  let: "s" := make2 t "len" in
  let: "l" := ref "elems" in
  let: "i" := mem.alloc int64T #() in
  (for: (λ: <>, int_lt (![int64T] "i") "len") ; (λ: <>, "i" <-[int64T] ![int64T] "i" + #(W64 1)) :=
     (λ: <>,
        do: (list.Match !"l" (λ: <>, #())
               (λ: "elem" "l_tail",
                  "l" <- "l_tail" ;;
                  elem_ref t "s" (![int64T] "i") <-[t] "elem")))) ;;
  "s"
.

End goose_lang.
End slice.

Global Opaque slice.ptr slice.len slice.cap slice.make3 slice.make2
  slice.elem_ref slice.slice slice.full_slice slice.for_range
  slice.copy slice._new_cap slice.append slice.literal.
