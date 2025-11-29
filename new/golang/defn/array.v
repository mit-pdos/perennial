From New.golang.defn Require Export predeclared.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

Class ArraySemantics `{!go.CoreComparisonDefinition} :=
{
  #[global]
  equals_array n t (H : go.IsComparable t) ::
    go.IsComparable (go.ArrayType n t);

  alloc_array n elem : alloc (go.ArrayType n elem) = alloc (go.ArrayType n elem); (* TODO *)
  load_array n elem_type :
    load (go.ArrayType n elem_type) =
    if decide (¬(0 ≤ n < 2^63-1)) then
      (λ: "l", AngelicExit #())%V
        (* the compiler guarantees that any compiled code does not have an array this size *)
    else
      (λ: "l",
         (rec: "recur" "n" :=
            if: "n" =⟨go.int⟩ #(W64 0) then (ArrayV [])
            else let: "array_so_far" := "recur" ("n" - #(W64 1)) in
                 let: "elem_addr" := IndexRef (go.ArrayType n elem_type) ("l", "n" - #(W64 1)) in
                 let: "elem_val" := GoLoad elem_type "elem_addr" in
                 ArrayAppend ("array_so_far", "elem_val")
         ) #(W64 n))%V;
  store_array n elem_type :
    store (go.ArrayType n elem_type) =
    (λ: "l" "v",
       foldl (λ str_so_far j,
                str_so_far;;
                let elem_addr := IndexRef (go.ArrayType n elem_type) ("l", #(W64 j)) in
                let elem_val := Index (go.ArrayType n elem_type) ("v", #(W64 n)) in
                GoStore elem_type (elem_addr, elem_val))
             (ArrayV []) (seqZ 0 n)
    )%V;

  index_ref_array n elem_type i l :
    index_ref (go.ArrayType n elem_type) i #l = #(array_index_ref elem_type i l);
  index_array n elem_type i l v (Hinrange : l !! (Z.to_nat i) = Some v):
    index (go.ArrayType n elem_type) i (ArrayV l) = (Val v);

  (* this only supports unkeyed array literals; goose will unfold them for now. *)
  composite_literal_array n elem_type (vs : list val) :
    composite_literal (go.ArrayType n elem_type) (ArrayV vs) =
    (#();; ArrayV vs)%E;

  array_index_ref_add t i j l :
    array_index_ref t (i + j) l = array_index_ref t j (array_index_ref t i l);
}.

End defs.
End go.
