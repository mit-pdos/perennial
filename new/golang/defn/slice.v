From New.golang.defn Require Export loop assume predeclared.

Module slice.
Section goose_lang.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

(* only for internal use, not an external model *)
Definition _new_cap : val :=
  λ: "len",
    let: "extra" := ArbitraryInt in
    if: "len" <⟨go.int⟩ ("len" +⟨go.int⟩ "extra") then "len" + "extra"
    else "len".

Definition for_range (elem_type : go.type) : val :=
  λ: "s" "body",
  let: "i" := GoAlloc go.int #() in
  for: (λ: <>, (![go.int] "i") <⟨go.int⟩
          (FuncResolve go.len [go.SliceType elem_type]) #() "s") ;
                      (λ: <>, "i" <-[go.int] (![go.int] "i") + #(W64 1)) :=
    (λ: <>, "body" (![go.int] "i") (![elem_type] (IndexRef (go.SliceType elem_type)) ("s", (![go.int] "i")))).

End goose_lang.
End slice.

Global Opaque slice.for_range.

Definition slice_index_ref {ext : ffi_syntax} `{!GoSemanticsFunctions} elem_type (i : Z) s : loc :=
  array_index_ref elem_type i s.(slice.ptr).

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.
Class SliceSemantics `{!GoSemanticsFunctions} :=
{
  #[global] go_zero_val_eq_slice elem_type :: go.GoZeroValEq (go.SliceType elem_type) slice.t;

  (* special cases *)
  #[global] is_go_op_go_equals_slice_nil_l elem_type s ::
    go.IsGoOp GoEquals (go.SliceType elem_type) (#slice.nil, #s)%V #(bool_decide (s = slice.nil));
  #[global] is_go_op_go_equals_slice_nil_r elem_type s ::
    go.IsGoOp GoEquals (go.SliceType elem_type) (#s, #slice.nil)%V #(bool_decide (s = slice.nil));

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
       let: "i" := GoAlloc go.int #() in
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
         InternalMakeSlice (#(Loc 1 0) +ₗ ArbitraryInt, "len", "cap")
       else
         let: "p" := (InternalDynamicArrayAlloc elem_type) "cap" in
         InternalMakeSlice ("p", "len", "cap"))%V;

  #[global] make2_slice elem_type ::
    FuncUnfold go.make2 [go.SliceType elem_type]
    (λ: "sz", FuncResolve go.make3 [go.SliceType elem_type] #() "sz" "sz")%V;

  index_ref_slice elem_type i s (Hrange : 0 ≤ i < sint.Z s.(slice.len)) :
    index_ref (go.SliceType elem_type) i #s = #(slice_index_ref elem_type i s);

  index_slice elem_type i (s : slice.t) :
    index (go.SliceType elem_type) i #s =
    GoLoad elem_type $ (Index $ go.SliceType elem_type) (#(W64 i), #s)%V;
  #[global] len_slice elem_type ::
    FuncUnfold go.len [go.SliceType elem_type]
    (λ: "s", InternalLen (go.SliceType elem_type) "s")%V;

  #[global] cap_slice elem_type ::
    FuncUnfold go.cap [go.SliceType elem_type]
    (λ: "s", InternalCap (go.SliceType elem_type) "s")%V;

  append_underlying t : functions go.append [t] = functions go.append [to_underlying t];
  #[global] append_slice elem_type ::
    FuncUnfold go.append [go.SliceType elem_type]
    (λ: "s" "x",
       let st : go.type := go.SliceType elem_type in
       let: "new_len" := sum_assume_no_overflow_signed (FuncResolve go.len [st] #() "s")
                           (FuncResolve go.len [st] #() "x") in
       if: (FuncResolve go.cap [st] #() "s") ≥⟨go.int⟩ "new_len" then
         (* "grow" s to include its capacity *)
         let: "s_new" := Slice st ("s", (#(W64 0), "new_len")) in
         (* copy "x" past the original "s" *)
         FuncResolve go.copy [st] #() (Slice st ("s_new", (FuncResolve go.len [st] #() "s", "new_len"))) "x";;
         "s_new"
       else
         let: "new_cap" := slice._new_cap "new_len" in
         let: "s_new" := FuncResolve go.make3 [st] #() "new_len" "new_cap" in
         FuncResolve go.copy [st] #() "s_new" "s" ;;
         FuncResolve go.copy [st] #() (Slice st ("s_new", (FuncResolve go.len [st] #() "s", "new_len"))) "x" ;;
         "s_new")%V;

  composite_literal_slice elem_type (vs : list val) :
    composite_literal (go.SliceType elem_type) (ArrayV vs) =
    if decide (Z.of_nat (length vs) < 2^63) then
      (let: "tmp" := GoAlloc (go.ArrayType (length vs) elem_type) #() in
       "tmp" <-[(go.ArrayType (length vs) elem_type)]
                CompositeLiteral (go.ArrayType (length vs) elem_type) (ArrayV vs);;
       Slice (go.ArrayType (length vs) elem_type) ("tmp", (#(W64 0), #(W64 (length vs))))
      )%E
    else AngelicExit #();

  array_index_ref_0 t l : array_index_ref t 0 l = l;
}.
End defs.
End go.
