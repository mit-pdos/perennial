From New.golang.defn Require Export mem loop.

Module slice.
(* FIXME: seal these functions *)
Section goose_lang.
Context `{ffi_syntax}.

Definition nil : val := slice_nil.
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
  else if: "cap" = #0 then InjL (#(Loc 1 0) +ₗ ArbitraryInt, Var "sz", Var "cap")
  else let: "p" := AllocN "cap" (zero_val t) in
       InjL (Var "p", Var "sz", Var "cap").

Definition make2 t : val :=
  λ: "sz", make3 t "sz" "sz".

(* computes `&s[i]` *)
Definition elem_ref t : val :=
  λ: "s" "i", if: "i" < len "s"
              then (ptr "s" +ₗ[t] "i")
              else Panic "slice index out-of-bounds".

Definition slice t : val :=
  λ: "a" "low" "high",
  if: (#0 ≤ "low") && ("low" ≤ "high") && ("high" ≤ cap "a") then
    (ptr "s" +ₗ[t] "low", "high" - "low", cap "s" - "low")
  else Panic "slice indices out of order"
.

Definition full_slice t : val :=
  λ: "a" "low" "high" "max",
  if: (#0 ≤ "low") && ("low" ≤ "high") && ("high" ≤ "max") && ("max" ≤ cap "a") then
    (ptr "s" +ₗ[t] "low", "high" - "low", "max" - "low")
  else Panic "slice indices out of order"
.

Definition for_range t : val :=
  λ: "s" "body",
  let: "i" := ref_ty uint64T (zero_val uint64T) in
  for: ("i" < len "s") ; Skip :=
    "body" "i" (![t] (elem_ref t "s"))
.

Definition copy t : val :=
  λ: "dst" "src",
  let: "i" := ref_ty uint64T (zero_val uint64T) in
  (for: (![uint64T] "i" < (len "dst")) && (![uint64T] "i" < (len "src")) ; Skip :=
   elem_ref t "dst" <-[t] ! (elem_ref t "src")) ;;
  ![uint64T] "i"
.

Definition append t : val :=
  λ: "s" "x",
  let: "s_new" := (if: (cap "s") > (len "s" + len "x") then
                     (slice t "s" #0 (len "s" + len "x"))
                   else
                     let: "extra" := ArbitraryInt in
                     let: "s_new" := make2 t (len "s" + len "x" + "extra") in
                     copy t "s_new" "s" ;;
                     "s_new"
                  ) in
  copy t (slice t "s_new" (len "s") (len "s_new")) "x" ;;
  "s_new".

(* FIXME: this shouldn't take len as input *)
(* Takes in a list of the specified length as input, and turns it into a
   heap-allocated slice. *)
Definition literal t : val :=
  λ: "len" "elems",
  let: "s" := make2 t "len" in
  let: "l" := ref "elems" in
  let: "i" := ref_ty uint64T (zero_val uint64T) in
  for: ![uint64T] "i" < "len" ; "i" <-[t] ![uint64T] "i" + #1 :=
    let: ("elem", "l_tail") := !"l"  in
    "l" <- "l_tail" ;;
    (elem_ref t "s" "i") <-[t] "elem"
.

End goose_lang.
End slice.
