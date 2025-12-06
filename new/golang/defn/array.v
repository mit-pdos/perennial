From New.golang.defn Require Export predeclared.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

Class ArraySemantics `{!GoSemanticsFunctions} :=
{
  #[global] array_set_step t V n (vs : array.t t V n) (i : w64) (v : V) ::
    go.IsGoStepPureDet ArraySet (#vs, (#i, #v))%V
    (# (array.mk t n (<[sint.nat i:=v]> (array.arr vs))));

  #[global] array_length_step vs ::
    go.IsGoStepPureDet ArrayLength (ArrayV vs)
    (if decide (length vs < 2 ^ 63) then #(W64 (length vs)) else AngelicExit (# ()));

  #[global] equals_array n t (H : go.IsComparable t) :: go.IsComparable (go.ArrayType n t);

  #[global] go_zero_val_eq_array ty V n `{!ZeroVal V} `{!go.GoZeroValEq ty V} ::
    go.GoZeroValEq (go.ArrayType n ty) (array.t ty V n);

  alloc_array n elem : alloc (go.ArrayType n elem) = alloc (go.ArrayType n elem); (* TODO *)
  load_array n elem_type :
    load (go.ArrayType n elem_type) =
    if decide (¬(0 ≤ n < 2^63-1)) then
      (λ: "l", AngelicExit #())%V
        (* the compiler guarantees that any compiled code does not have an array this size *)
    else
      (λ: "l",
         (rec: "recur" "n" :=
            if: "n" =⟨go.int⟩ #(W64 0) then go_zero_val (go.ArrayType n elem_type)
            else let: "array_so_far" := "recur" ("n" - #(W64 1)) in
                 let: "elem_addr" := IndexRef (go.ArrayType n elem_type) ("l", "n" - #(W64 1)) in
                 let: "elem_val" := GoLoad elem_type "elem_addr" in
                 ArraySet ("array_so_far", ("n" - #(W64 1), "elem_val"))
         ) #(W64 n))%V;
  store_array n elem_type :
    store (go.ArrayType n elem_type) =
    (λ: "l" "v",
       foldl (λ str_so_far j,
                str_so_far;;
                let elem_addr := IndexRef (go.ArrayType n elem_type) ("l", #(W64 j)) in
                let elem_val := Index (go.ArrayType n elem_type) ("v", #(W64 n)) in
                GoStore elem_type (elem_addr, elem_val))
             (#()) (seqZ 0 n)
    )%V;

  index_ref_array n elem_type i l :
    index_ref (go.ArrayType n elem_type) i #l = #(array_index_ref elem_type i l);
  index_array n elem_type i V (a : array.t elem_type V n) v
    (Hinrange : (array.arr a) !! (Z.to_nat i) = Some v):
    index (go.ArrayType n elem_type) i #a = #v;

  composite_literal_array n elem_type kvs :
    composite_literal (go.ArrayType n elem_type) (LiteralValue kvs) =
    (foldl (λ '(cur_index, expr_so_far) ke,
             match ke with
             | KeyedElement None (ElementExpression e) =>
                 (cur_index + 1, ArraySet (expr_so_far, (#(W64 cur_index), e))%E)
             | KeyedElement None (ElementLiteralValue l) =>
                 (cur_index + 1,
                    ArraySet (expr_so_far, (#(W64 cur_index), CompositeLiteral elem_type $ LiteralValue l))%E)
             | KeyedElement (Some (KeyInteger cur_index)) (ElementExpression e) =>
                 (cur_index + 1, ArraySet (expr_so_far, (#(W64 cur_index), e))%E)
             | KeyedElement (Some (KeyInteger cur_index)) (ElementLiteralValue l) =>
                 (cur_index + 1,
                    ArraySet (expr_so_far, (#(W64 cur_index), CompositeLiteral elem_type $ LiteralValue l))%E)
             | _ => (0, Panic "invalid array literal")
             end
      ) (0, Val (go_zero_val (go.ArrayType n elem_type))) kvs).2;

  #[global] slice_array_step n elem_type p low high ::
    go.IsGoStepPureDet (Slice $ go.ArrayType n elem_type) (#p, (#low, #high))%V
       (if decide (0 ≤ sint.Z low ≤ sint.Z high ≤ n) then
          #(slice.mk (array_index_ref elem_type (word.signed low) p)
              (word.sub high low)
              (word.sub (W64 n) low))
        else Panic "slice bounds out of range");

  #[global] full_slice_array_step_pure n elem_type p low high max ::
    go.IsGoStepPureDet (FullSlice (go.ArrayType n elem_type))
    (#p, (#low, #high, #max))%V
    (if decide (0 ≤ sint.Z low ≤ sint.Z high ≤ sint.Z max ∧ sint.Z max ≤ n) then
       #(slice.mk (array_index_ref elem_type (sint.Z low) p)
           (word.sub high low) (word.sub max low))
     else Panic "slice bounds out of range");

  array_index_ref_add t i j l :
    array_index_ref t (i + j) l = array_index_ref t j (array_index_ref t i l);
}.

End defs.
End go.
