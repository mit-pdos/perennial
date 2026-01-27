From New.golang.defn Require Export loop assume predeclared.

Definition slice_index_ref {ext : ffi_syntax} `{!GoSemanticsFunctions} elem_type (i : Z) s : loc :=
  array_index_ref elem_type i s.(slice.ptr).

Module slice.
Section goose_lang.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext} `{!GoSemanticsFunctions}.

Definition slice (sl : slice.t) (V : Type) (low high : u64) : slice.t :=
  slice.mk (slice_index_ref V (sint.Z low) sl) (word.sub high low) (word.sub sl.(slice.cap) low).

Definition full_slice (sl : slice.t) (V : Type) (low high max : u64) : slice.t :=
  slice.mk (slice_index_ref V (sint.Z low) sl) (word.sub high low) (word.sub max low).

(* only for internal use, not an external model *)
Definition _new_cap : val :=
  λ: "len",
    let: "extra" := ArbitraryInt in
    if: "len" <⟨go.int⟩ ("len" +⟨go.int⟩ "extra") then "len" + "extra"
    else "len".

Definition for_range (elem_type : go.type) : val :=
  λ: "s" "body",
  let: "i" := GoAlloc go.int #(W64 0) in
  for: (λ: <>, (![go.int] "i") <⟨go.int⟩
          (FuncResolve go.len [go.SliceType elem_type]) #() "s") ;
                      (λ: <>, "i" <-[go.int] (![go.int] "i") + #(W64 1)) :=
    (λ: <>, "body" (![go.int] "i") (![elem_type] (IndexRef (go.SliceType elem_type) ("s", (![go.int] "i"))))).

End goose_lang.
End slice.

Global Opaque slice.for_range.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

Definition array_literal_size kvs : Z :=
  let '(last, m) := (foldl (λ '(cur_index, max_so_far) ke,
                              match ke with
                              | KeyedElement None _ => (cur_index + 1, max_so_far)
                              | KeyedElement (Some (KeyInteger cur_index')) _ =>
                                  (cur_index' + 1, cur_index `max` max_so_far)
                              | _ => (-1, -1)
                              end
                       ) (0, 0) kvs) in
  last `max` m.

Class SliceSemantics `{!GoSemanticsFunctions} :=
{
  #[global] internal_len_step s ::
    ⟦InternalSliceLen, #s⟧ ⤳ #(s.(slice.len));
  #[global] internal_cap_step s ::
    ⟦InternalSliceCap, #s⟧ ⤳ #(s.(slice.cap));
  #[global] internal_make_slice_step p l c ::
    ⟦InternalMakeSlice, (#p, #l, #c)⟧ ⤳
    #(slice.mk p l c);
  #[global] internal_dynamic_array_alloc_step et (n : w64) ::
    ⟦InternalDynamicArrayAlloc et, #n⟧ ⤳
    (GoAlloc (go.ArrayType (sint.Z n) et) (GoZeroVal (go.ArrayType (sint.Z n) et) #()));
  #[global] slice_slice_step_pure elem_type s low high `{!ZeroVal V} `{!go.TypeRepr elem_type V} ::
    ⟦Slice (go.SliceType elem_type), (#s, #low, #high)⟧ ⤳
    (if decide (0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z s.(slice.cap)) then
       #(slice.slice s V low high)
     else Panic "slice bounds out of range");
  #[global] full_slice_slice_step_pure elem_type s low high max `{!ZeroVal V}
    `{!go.TypeRepr elem_type V} ::
    ⟦FullSlice (go.SliceType elem_type), (#s, #low, #high, #max)⟧ ⤳
    (if decide (0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z max ∧ sint.Z max ≤ sint.Z s.(slice.cap)) then
       #(slice.full_slice s V low high max)
     else Panic "slice bounds out of range");

  #[global] type_repr_slice elem_type :: go.TypeRepr (go.SliceType elem_type) slice.t;

  (* special case for slice equality *)
  #[global] is_go_op_go_equals_slice_nil_l elem_type s ::
    ⟦GoOp GoEquals (go.SliceType elem_type), (#slice.nil, #s)⟧ ⤳[under] #(bool_decide (s = slice.nil));
  #[global] is_go_op_go_equals_slice_nil_r elem_type s ::
    ⟦GoOp GoEquals (go.SliceType elem_type), (#s, #slice.nil)⟧ ⤳[under] #(bool_decide (s = slice.nil));

  #[global] clear_slice elem_type ::
    FuncUnfold go.clear [go.SliceType elem_type]
    (λ: "sl",
       let st : go.type := go.SliceType elem_type in
       let: "zero_sl" := FuncResolve go.make2 [st] #() (FuncResolve go.len [st] #() "sl") in
       FuncResolve go.copy [st] #() "sl" "zero_sl";;
    #())%V;

  #[global] copy_slice elem_type ::
    FuncUnfold go.copy [go.SliceType elem_type]
    (λ: "dst" "src",
       let st : go.type := go.SliceType elem_type in
       let: "i" := GoAlloc go.int (GoZeroVal go.int #()) in
       (for: (λ: <>, (![go.int] "i" <⟨go.int⟩ FuncResolve go.len [st] #() "dst") &&
                (![go.int] "i" <⟨go.int⟩ FuncResolve go.len [st] #() "src")) ; (λ: <>, Skip) :=
          (λ: <>,
             do: (let: "i_val" := ![go.int] "i" in
                  IndexRef st ("dst", "i_val")
                      <-[elem_type] ![elem_type] (IndexRef st ("src", "i_val"));;
                  "i" <-[go.int] "i_val" + #(W64 1))));;
       ![go.int] "i")%V;


  #[global] make3_slice elem_type ::
    FuncUnfold go.make3 [go.SliceType elem_type]
    (λ: "len" "cap",
       if: ("cap" <⟨go.int⟩ "len") then Panic "makeslice: cap out of range" else #();;
       if: ("len" <⟨go.int⟩ #(W64 0)) then Panic "makeslice: len out of range" else #();;
       if: "cap" =⟨go.int⟩ #(W64 0) then
         (* XXX: this computes a nondeterministic unallocated address by using
            "(Loc 1 0) +ₗ ArbiraryInt"*)
         InternalMakeSlice (#(Loc 1 0) +⟨go.PointerType elem_type⟩ ArbitraryInt, "len", "cap")
       else
         let: "p" := (InternalDynamicArrayAlloc elem_type) "cap" in
         InternalMakeSlice ("p", "len", "cap"))%V;
  #[global] is_go_op_pointer_plus t (l : loc) (x : w64) ::
    ⟦GoOp GoPlus (go.PointerType t), (#l, #x)⟧ ⤳[under] (#(loc_add l (sint.Z x)));

  #[global] make2_slice elem_type ::
    FuncUnfold go.make2 [go.SliceType elem_type]
    (λ: "sz", FuncResolve go.make3 [go.SliceType elem_type] #() "sz" "sz")%V;

  #[global] index_ref_slice elem_type (i : w64) s `{!ZeroVal V} `{!go.TypeRepr elem_type V} ::
    ⟦IndexRef (go.SliceType elem_type), (#s, #i)⟧ ⤳[under]
    (if decide (0 ≤ sint.Z i < sint.Z s.(slice.len)) then
       #(slice_index_ref V (sint.Z i) s)
     else Panic "slice index out of bounds");

  #[global] index_slice elem_type (i : w64) (s : slice.t) ::
    ⟦Index (go.SliceType elem_type), (#s, #i)⟧ ⤳[under]
    (GoLoad elem_type $ (IndexRef $ go.SliceType elem_type) (#i, #s)%V);

  #[global] len_slice elem_type ::
    FuncUnfold go.len [go.SliceType elem_type]
    (λ: "s", InternalSliceLen "s")%V;

  #[global] cap_slice elem_type ::
    FuncUnfold go.cap [go.SliceType elem_type]
    (λ: "s", InternalSliceCap "s")%V;

  append_underlying t : functions go.append [t] = functions go.append [underlying t];
  #[global] append_slice elem_type ::
    FuncUnfold go.append [go.SliceType elem_type]
    (λ: "s" "x",
       let st : go.type := go.SliceType elem_type in
       let: "new_len" := sum_assume_no_overflow_signed (FuncResolve go.len [st] #() "s")
                           (FuncResolve go.len [st] #() "x") in
       if: (FuncResolve go.cap [st] #() "s") ≥⟨go.int⟩ "new_len" then
         (* "grow" s to include its capacity *)
         let: "s_new" := Slice st ("s", #(W64 0), "new_len") in
         (* copy "x" past the original "s" *)
         FuncResolve go.copy [st] #() (Slice st ("s_new", FuncResolve go.len [st] #() "s", "new_len")) "x";;
         "s_new"
       else
         let: "new_cap" := slice._new_cap "new_len" in
         let: "s_new" := FuncResolve go.make3 [st] #() "new_len" "new_cap" in
         FuncResolve go.copy [st] #() "s_new" "s" ;;
         FuncResolve go.copy [st] #() (Slice st ("s_new", FuncResolve go.len [st] #() "s", "new_len")) "x" ;;
         "s_new")%V;

  #[global] composite_literal_slice elem_type kvs ::
    ⟦CompositeLiteral (go.SliceType elem_type), (LiteralValueV kvs)⟧ ⤳[under]
    (let len := array_literal_size kvs in
    (let: "tmp" := GoAlloc (go.ArrayType len elem_type) (GoZeroVal (go.ArrayType len elem_type) #()) in
     "tmp" <-[(go.ArrayType len elem_type)]
              CompositeLiteral (go.ArrayType len elem_type) (LiteralValue kvs);;
     Slice (go.ArrayType len elem_type) ("tmp", #(W64 0), #(W64 len))
    )%E);

  array_index_ref_0 t l : array_index_ref t 0 l = l;
}.
End defs.
End go.
