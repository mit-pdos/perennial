From New.golang.defn Require Export mem loop assume exception typing list.

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
  if: "cap" < "sz" then Panic "NewSlice with cap smaller than len"
  else if: "cap" = #(W64 0) then InjL (#(Loc 1 0) +ₗ ArbitraryInt, Var "sz", Var "cap")
  else let: "p" := AllocN "cap" (zero_val t) in
       InjL (Var "p", Var "sz", Var "cap").

Definition make2 t : val :=
  λ: "sz", make3 t "sz" "sz".

(* computes `&s[i]` *)
Definition elem_ref t : val :=
  λ: "s" "i", if: "i" < len "s"
              then (ptr "s" +ₗ[t] "i")
              else Panic "slice index out-of-bounds".

(* s[a:b], as well as s[a:] = s[a:len(s)] and s[:b] = s[0:b] *)
Definition slice t : val :=
  λ: "s" "low" "high",
  if: (#(W64 0) ≤ "low") && ("low" ≤ "high") && ("high" ≤ cap "s") then
    InjL (ptr "s" +ₗ[t] "low", "high" - "low", cap "s" - "low")
  else Panic "slice indices out of order"
.

(* s[a:b:c] (picking a specific capacity c) *)
Definition full_slice t : val :=
  λ: "s" "low" "high" "max",
  if: (#(W64 0) ≤ "low") && ("low" ≤ "high") && ("high" ≤ "max") && ("max" ≤ cap "s") then
    InjL (ptr "s" +ₗ[t] "low", "high" - "low", "max" - "low")
  else Panic "slice indices out of order"
.

Definition for_range t : val :=
  λ: "s" "body",
  let: "i" := ref_ty uint64T #(W64 0) in
  for: (λ: <>, ![uint64T] "i" < len "s") ; (λ: <>, "i" <-[uint64T] (![uint64T] "i") + #(W64 1)) :=
    (λ: <>, "body" (![uint64T] "i") (![t] (elem_ref t "s" (![uint64T] "i"))))
.

Definition copy t : val :=
  λ: "dst" "src",
  let: "i" := ref_ty uint64T (zero_val uint64T) in
  (for: (λ: <>, (![uint64T] "i" < len "dst") && (![uint64T] "i" < (len "src"))) ; (λ: <>, Skip) :=
    (λ: <>,
    do: (let: "i_val" := ![uint64T] "i" in
      elem_ref t "dst" "i_val" <-[t] ![t] (elem_ref t "src" "i_val");;
      "i" <-[uint64T] "i_val" + #(W64 1))));;
  ![uint64T] "i"
.

Definition append t : val :=
  λ: "s" "x",
  let: "new_len" := sum_assume_no_overflow (len "s") (len "x") in
  if: (cap "s") ≥ "new_len" then
    (* "grow" s to include its capacity *)
    let: "s_new" := slice t "s" #(W64 0) "new_len" in
    (* copy "x" past the original "s" *)
    copy t (slice t "s_new" (len "s") "new_len") "x";;
    "s_new"
  else
    let: "extra" := ArbitraryInt in
    let: "new_cap" := sum_assume_no_overflow "new_len" "extra" in
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
  let: "i" := ref_ty uint64T (zero_val uint64T) in
  (for: (λ: <>, ![uint64T] "i" < "len") ; (λ: <>, "i" <-[uint64T] ![uint64T] "i" + #(W64 1)) :=
     (λ: <>,
        do: (list.Match !"l" (λ: <>, #())
               (λ: "elem" "l_tail",
                  "l" <- "l_tail" ;;
                  (elem_ref t "s" (![uint64T] "i")) <-[t] "elem")))) ;;
  "s"
.

End goose_lang.
End slice.

Global Opaque slice.ptr slice.len slice.cap slice.make3 slice.make2
  slice.elem_ref slice.slice slice.full_slice slice.for_range
  slice.copy slice.append slice.literal.
