From New.golang.defn Require Export predeclared.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

Class ArraySemantics `{!GoSemanticsFunctions} :=
{
  #[global] array_set_step V n (vs : array.t V n) (i : w64) (v : V) ::
    ⟦ArraySet, (#vs, (#i, #v))⟧ ⤳
    (# (array.mk n (<[sint.nat i:=v]> (array.arr vs))));

  #[global] array_length_step vs ::
    ⟦ArrayLength, (ArrayV vs)⟧ ⤳
    (if decide (length vs < 2 ^ 63) then #(W64 (length vs)) else AngelicExit (# ()));

  #[global] equals_array n t (H : go.IsComparable t) :: go.IsComparable (go.ArrayType n t);

  #[global] type_repr_array ty V n `{!ZeroVal V} `{!go.TypeRepr ty V} ::
    go.TypeRepr (go.ArrayType n ty) (array.t V n);

  (* TODO: implement alloc_array *)
  #[global] alloc_array n elem v :: ⟦GoAlloc (go.ArrayType n elem), v⟧ ⤳[internal] AngelicExit #();

  #[global] load_array n elem_type l ::
    ⟦GoLoad (go.ArrayType n elem_type), l⟧ ⤳[internal]
    (if decide (¬(0 ≤ n < 2^63-1)) then
      AngelicExit #()
    else
      (rec: "recur" "n" :=
            if: "n" =⟨go.int⟩ #(W64 0) then GoZeroVal (go.ArrayType n elem_type) #()
            else let: "array_so_far" := "recur" ("n" - #(W64 1)) in
                 let: "elem_addr" := IndexRef (go.ArrayType n elem_type) (l, "n" - #(W64 1)) in
                 let: "elem_val" := GoLoad elem_type "elem_addr" in
                 ArraySet ("array_so_far", ("n" - #(W64 1), "elem_val"))
         ) #(W64 n))%E;

  #[global] store_array n elem_type l v ::
    ⟦GoStore (go.ArrayType n elem_type), (l, v)⟧ ⤳[internal]
    (foldl (λ str_so_far j,
                str_so_far;;
                let elem_addr := IndexRef (go.ArrayType n elem_type) (l, #(W64 j)) in
                let elem_val := Index (go.ArrayType n elem_type) (v, #(W64 n)) in
                GoStore elem_type (elem_addr, elem_val))
             (#()) (seqZ 0 n)
    )%E;


  #[global] index_ref_array n elem_type i l V `{!ZeroVal V} `{!go.TypeRepr elem_type V} ::
    go.GoExprEq (index_ref (go.ArrayType n elem_type) i #l)
      (if decide (i < n) then #(array_index_ref V i l)
       else Panic "index out of range");
  #[global] index_array n elem_type i V `{!ZeroVal V} `{!go.TypeRepr elem_type V} (a : array.t V n) ::
    go.GoExprEq (index (go.ArrayType n elem_type) i #a)
      (match (array.arr a) !! (Z.to_nat i) with
       | Some v => #v
       | None => Panic "index out of range"
       end);

  #[global] composite_literal_array n elem_type kvs ::
    go.GoExprEq (composite_literal (go.ArrayType n elem_type) (LiteralValueV kvs))
    (foldl (λ '(cur_index, expr_so_far) ke,
             match ke with
             | KeyedElement None (ElementExpression from e) =>
                 (cur_index + 1, ArraySet (expr_so_far, (#(W64 cur_index), Convert from elem_type e))%E)
             | KeyedElement None (ElementLiteralValue l) =>
                 (cur_index + 1,
                    ArraySet (expr_so_far, (#(W64 cur_index), CompositeLiteral elem_type $ LiteralValue l))%E)
             | KeyedElement (Some (KeyInteger cur_index)) (ElementExpression from e) =>
                 (cur_index + 1, ArraySet (expr_so_far, (#(W64 cur_index), Convert from elem_type e))%E)
             | KeyedElement (Some (KeyInteger cur_index)) (ElementLiteralValue l) =>
                 (cur_index + 1,
                    ArraySet (expr_so_far, (#(W64 cur_index), CompositeLiteral elem_type $ LiteralValue l))%E)
             | _ => (0, Panic "invalid array literal")
             end
      ) (0, (GoZeroVal (go.ArrayType n elem_type) #())) kvs).2;

  #[global] slice_array_step n elem_type p low high `{!ZeroVal V} `{!go.TypeRepr elem_type V} ::
    ⟦Slice $ go.ArrayType n elem_type, (#p, #low, #high)⟧ ⤳
       (if decide (0 ≤ sint.Z low ≤ sint.Z high ≤ n) then
          #(slice.mk (array_index_ref V (word.signed low) p)
              (word.sub high low)
              (word.sub (W64 n) low))
        else Panic "slice bounds out of range");

  #[global] full_slice_array_step_pure n elem_type p low high max `{!ZeroVal V}
    `{!go.TypeRepr elem_type V} ::
    ⟦FullSlice (go.ArrayType n elem_type), (#p, #low, #high, #max)⟧ ⤳
    (if decide (0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z max ∧ sint.Z max ≤ n) then
       #(slice.mk (array_index_ref V (sint.Z low) p)
           (word.sub high low) (word.sub max low))
     else Panic "slice bounds out of range");

  array_index_ref_add t i j l :
    array_index_ref t (i + j) l = array_index_ref t j (array_index_ref t i l);

  (* For disk FFI proof. *)
  array_index_ref_add_loc_add i l :
    array_index_ref w8 i l = loc_add l i;

  #[global] into_val_inj_array V n {inj_V : go.IntoValInj V} ::
    go.IntoValInj (array.t V n);
}.

End defs.
End go.
