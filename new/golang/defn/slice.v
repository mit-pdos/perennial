From Perennial Require Import base.
From New.golang.defn Require Export loop assume predeclared.

Definition slice_index_ref `{GoContext} (elem_type : go.type) (i : Z) (s : slice.t) : loc :=
  array_index_ref elem_type i s.(slice.ptr).

Module slice.
Section goose_lang.
Context `{ffi_syntax}.

(* only for internal use, not an external model *)
Definition _new_cap : val :=
  λ: "len",
    let: "extra" := ArbitraryInt in
    if: "len" <⟨go.int⟩ ("len" + "extra") then "len" + "extra"
    else "len".

Definition for_range (elem_type : go.type) : val :=
  λ: "s" "body",
  let: "i" := GoAlloc go.int #() in
  for: (λ: <>, (![go.int] "i") <⟨go.int⟩
          (FuncResolve go.len [go.TypeLit $ go.SliceType elem_type]) #() "s") ;
                      (λ: <>, "i" <-[go.int] (![go.int] "i") + #(W64 1)) :=
    (λ: <>, "body" (![go.int] "i") (![elem_type] (IndexRef (go.SliceType elem_type)) ("s", (![go.int] "i"))))
.

(* Takes in a list as input, and turns it into a heap-allocated slice. *)
Definition literal (elem_type : go.type) (len : w64) : val :=
  λ: "elems",
  let st : go.type := go.SliceType elem_type in
  let: "s" := FuncResolve go.make2 [st] #() #len in
  let: "l" := ref "elems" in
  let: "i" := GoAlloc go.int #() in
  (for: (λ: <>, (![go.int] "i") <⟨go.int⟩ #len) ; (λ: <>, "i" <-[go.int] ![go.int] "i" + #(W64 1)) :=
     (λ: <>,
        do: (IndexRef st ("s", (![go.int] "i")) <-[elem_type]
                (Index (go.ArrayType (sint.Z len) elem_type) ("elems", ![go.int] "i"))))) ;;
  "s".

End goose_lang.
End slice.

Global Opaque slice.for_range slice.literal.

Module go.
Class SliceSemantics {ext : ffi_syntax} `{!GoContext} :=
{
  equals_slice_l t s :
    go_equals (go.SliceType t) #s #slice.nil = Some $ bool_decide (s = slice.nil);
  equals_slice_r t s :
    go_equals (go.SliceType t) #slice.nil #s = Some $ bool_decide (s = slice.nil);

  make3_slice elem_type :
    #(functions go.make3 [go.TypeLit $ go.SliceType elem_type]) =
    (λ: "len" "cap",
       if: ("cap" <⟨go.int⟩ "len") then Panic "makeslice: cap out of range" else #();;
       if: ("len" <⟨go.int⟩ #(W64 0)) then Panic "makeslice: len out of range" else #();;
       if: "cap" =⟨go.int⟩ #(W64 0) then
         (* XXX: this computes a nondeterministic unallocated address by using
            "(Loc 1 0) +ₗ ArbiraryInt"*)
         InternalMakeSlice (#(Loc 1 0) +ₗ ArbitraryInt, "len", "cap")
       else
         let: "p" := (InternalDynamicArrayAlloc elem_type) "cap" in
         InternalMakeSlice ("p", "len", "cap"))%V;

  make2_slice elem_type :
    #(functions go.make2 [go.TypeLit $ go.SliceType elem_type]) =
    (λ: "sz", FuncResolve go.make3 [go.TypeLit $ go.SliceType elem_type] #() "sz" "sz")%V;

  index_ref_slice elem_type i s (Hrange : 0 ≤ i < sint.Z s.(slice.len)) :
    index_ref (go.SliceType elem_type) i #s = #(slice_index_ref elem_type i s);

  index_slice_slice elem_type i (s : slice.t) :
    index (go.SliceType elem_type) i #s =
    GoLoad elem_type $ (Index $ go.SliceType elem_type) (#(W64 i), #s)%V;
  len_slice elem_type :
    #(functions go.len [go.TypeLit $ go.SliceType elem_type]) =
    (λ: "s", InternalLen (go.SliceType elem_type) "s")%V;

  cap_slice elem_type :
    #(functions go.cap [go.TypeLit $ go.SliceType elem_type]) =
    (λ: "s", InternalCap (go.SliceType elem_type) "s")%V;

  copy_underlying t : functions go.copy [t] = functions go.copy [to_underlying t];
  copy_slice elem_type :
    #(functions go.copy [go.TypeLit $ go.SliceType elem_type]) =
    (λ: "dst" "src",
       let st : go.type := go.SliceType elem_type in
       let: "i" := GoAlloc go.int #() in
       (for: (λ: <>, (![go.int] "i") <⟨go.int⟩ (FuncResolve go.len [st] #() "dst") &&
                ((![go.int] "i") <⟨go.int⟩ (FuncResolve go.len [st] #() "src"))) ; (λ: <>, Skip) :=
          (λ: <>,
             do: (let: "i_val" := ![go.int] "i" in
                  IndexRef st ("dst", "i_val")
                      <-[elem_type] ![elem_type] (IndexRef st ("src", "i_val"));;
                  "i" <-[go.int] "i_val" + #(W64 1))));;
       ![go.int] "i")%V;

  append_underlying t : functions go.append [t] = functions go.append [to_underlying t];
  append_slice elem_type :
    #(functions go.append [go.TypeLit $ go.SliceType elem_type]) =
    (λ: "s" "x",
       let st : go.type := go.SliceType elem_type in
       let: "new_len" := sum_assume_no_overflow_signed (FuncResolve go.len [st] #() "s")
                           (FuncResolve go.len [st] #() "x") in
       if: (FuncResolve go.cap [st] #() "s") ≥⟨go.int⟩ "new_len" then
         (* "grow" s to include its capacity *)
         let: "s_new" := Slice st "s" #(W64 0) "new_len" in
         (* copy "x" past the original "s" *)
         FuncResolve go.copy [st] #() (Slice st "s_new" (FuncResolve go.len [st] #() "s") "new_len") "x";;
         "s_new"
       else
         let: "new_cap" := slice._new_cap "new_len" in
         let: "s_new" := FuncResolve go.make3 [st] #() "new_len" "new_cap" in
         FuncResolve go.copy [st] #() "s_new" "s" ;;
         FuncResolve go.copy [st] #() (Slice st "s_new" (FuncResolve go.len [st] #() "s") "new_len") "x" ;;
         "s_new")%V;

  array_index_ref_0 t l : array_index_ref t 0 l = l;
}.
End go.
