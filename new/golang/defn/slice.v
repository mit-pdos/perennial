From Perennial Require Import base.
From New.golang.defn Require Export loop assume.

Definition slice_index_ref `{GoContext} (elem_type : go.type) (i : Z) (s : slice.t) : loc :=
  array_index_ref elem_type i s.(slice.ptr).

Module slice.
Section goose_lang.
Context `{ffi_syntax}.

(* only for internal use, not an external model *)
Definition _new_cap : val :=
  λ: "len",
    let: "extra" := ArbitraryInt in
    if: int_leq "len" ("len" + "extra") then "len" + "extra"
    else "len".

Definition for_range (elem_type : go.type) : val :=
  λ: "s" "body",
  let: "i" := GoAlloc go.int64 #() in
  for: (λ: <>, int_lt (![go.int64] "i")
          (FuncCall len [go.TypeLit $ go.SliceType elem_type]) "s") ;
                      (λ: <>, "i" <-[go.int64] (![go.int64] "i") + #(W64 1)) :=
    (λ: <>, "body" (![go.int64] "i") (![elem_type] (IndexRef (go.SliceType elem_type)) "s" (![go.int64] "i")))
.

(* Takes in a list as input, and turns it into a heap-allocated slice. *)
Definition literal (elem_type : go.type) (len : Z) : val :=
  λ: "elems",
  let st : go.type := go.SliceType elem_type in
  let: "s" := FuncCall make2 [st] "len" in
  let: "l" := ref "elems" in
  let: "i" := GoAlloc go.int64 #() in
  (for: (λ: <>, int_lt (![go.int64] "i") "len") ; (λ: <>, "i" <-[go.int64] ![go.int64] "i" + #(W64 1)) :=
     (λ: <>,
        do: (IndexRef st "s" (![go.int64] "i") <-[elem_type] (Index (go.ArrayType len elem_type) "elems" "i")))) ;;
  "s".

End goose_lang.
End slice.

Global Opaque slice.for_range slice.literal.

Module go.
Class SliceSemantics {ext : ffi_syntax} `{!GoContext} :=
{
  make3_slice elem_type :
    #(functions make3 [go.TypeLit $ go.SliceType elem_type]) =
    (λ: "len" "cap",
       if: (int_lt "cap" "len") then Panic "makeslice: cap out of range" else #();;
       if: (int_lt "len" #(W64 0)) then Panic "makeslice: len out of range" else #();;
       if: "cap" = #(W64 0) then
         (* XXX: this computes a nondeterministic unallocated address by using
            "(Loc 1 0) +ₗ ArbiraryInt"*)
         InternalMakeSlice (#(Loc 1 0) +ₗ ArbitraryInt, "len", "cap")
       else
         let: "p" := (InternalDynamicArrayAlloc elem_type) "cap" in
         InternalMakeSlice ("p", "len", "cap"))%V;

  make2_slice elem_type :
    #(functions make2 [go.TypeLit $ go.SliceType elem_type]) =
    (λ: "sz", FuncCall make3 [go.TypeLit $ go.SliceType elem_type] #() "sz" "sz")%V;

  index_ref_slice elem_type i s (Hrange : 0 ≤ i < sint.Z s.(slice.len)) :
    index_ref (go.SliceType elem_type) i #s = #(slice_index_ref elem_type i s);

  index_slice_slice elem_type i (s : slice.t) :
    index (go.SliceType elem_type) i #s =
    GoLoad elem_type $ (Index $ go.SliceType elem_type) #(W64 i) #s;
  len_slice elem_type :
    #(functions len [go.TypeLit $ go.SliceType elem_type]) =
    (λ: "s", InternalLen (go.SliceType elem_type) "s")%V;

  cap_slice elem_type :
    #(functions cap [go.TypeLit $ go.SliceType elem_type]) =
    (λ: "s", InternalCap (go.SliceType elem_type) "s")%V;

  copy_underlying t : functions copy [t] = functions copy [to_underlying t];
  copy_slice elem_type :
    #(functions copy [go.TypeLit $ go.SliceType elem_type]) =
    (λ: "dst" "src",
       let st : go.type := go.SliceType elem_type in
       let: "i" := GoAlloc go.int64 #() in
       (for: (λ: <>, int_lt (![go.int64] "i") (FuncCall len [st] "dst") &&
                (int_lt (![go.int64] "i") (FuncCall len [st] "src"))) ; (λ: <>, Skip) :=
          (λ: <>,
             do: (let: "i_val" := ![go.int64] "i" in
                  IndexRef st "dst" "i_val"
                      <-[elem_type] ![elem_type] (IndexRef st "src" "i_val");;
                  "i" <-[go.int64] "i_val" + #(W64 1))));;
       ![go.int64] "i")%V;

  append_underlying t : functions append [t] = functions append [to_underlying t];
  append_slice elem_type :
    #(functions append [go.TypeLit $ go.SliceType elem_type]) =
    (λ: "s" "x",
       let st : go.type := go.SliceType elem_type in
       let: "new_len" := sum_assume_no_overflow_signed (FuncCall len [st] "s")
                           (FuncCall len [st] "x") in
       if: (FuncCall cap [st] "s") ≥ "new_len" then
         (* "grow" s to include its capacity *)
         let: "s_new" := Slice st "s" #(W64 0) "new_len" in
         (* copy "x" past the original "s" *)
         FuncCall copy [st] (Slice st "s_new" (FuncCall len [st] "s") "new_len") "x";;
         "s_new"
       else
         let: "new_cap" := slice._new_cap "new_len" in
         let: "s_new" := FuncCall make3 [st] "new_len" "new_cap" in
         FuncCall copy [st] "s_new" "s" ;;
         FuncCall copy [st] (Slice st "s_new" (FuncCall len [st] "s") "new_len") "x" ;;
         "s_new")%V;

  array_index_ref_0 t l : array_index_ref t 0 l = l;
}.
End go.
