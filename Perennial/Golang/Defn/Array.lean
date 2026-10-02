/-
Port of `new/golang/defn/array.v`.
-/
import Perennial.Golang.Defn.Predeclared

namespace Perennial

namespace go
section defs
variable [ffi_syntax] [GoLocalContext] [GoGlobalContext]

class ArraySemantics [GoSemanticsFunctions] : Prop where
  array_set_step (V : Type) (n : Int) (vs : array.t V n) (i : w64) (v : V) :
    ⟦ArraySet, (#vs, (#i, #v))⟧ ⤳
    #(array.mk n (vs.arr.set (sint.nat i) v))

  array_length_step (vs : List val) :
    ⟦ArrayLength, (ArrayV vs)⟧ ⤳
    (if vs.length < 2 ^ 63 then #(W64 vs.length) else AngelicExit #())

  equals_array (n : Int) (t : go.type) [H : ⟦CheckComparable t, #()⟧ ⤳[under] #()] :
    ⟦CheckComparable (go.ArrayType n t), #()⟧ ⤳[under] #()

  type_repr_array (ty : go.type) (V : Type) (n : Int) [ZeroVal V] [TypeRepr ty V] :
    go.TypeReprUnderlying (go.ArrayType n ty) (array.t V n)

  -- TODO: implement alloc_array
  alloc_array (n : Int) (elem : go.type) (v : val) :
    ⟦GoAlloc (go.ArrayType n elem), v⟧ ⤳[internal_under] AngelicExit #()

  load_array (n : Int) (elem_type : go.type) (l : val) :
    ⟦GoLoad (go.ArrayType n elem_type), l⟧ ⤳[internal_under]
    (if ¬(0 ≤ n ∧ n < 2^63-1) then
      gl(AngelicExit #())
    else
      gl((rec: "recur" "n" :=
            if: "n" =⟨go.int⟩ #(W64 0) then GoZeroVal (go.ArrayType n elem_type) #()
            else let: "array_so_far" := "recur" ("n" -⟨go.int⟩ #(W64 1)) in
                 let: "elem_addr" := IndexRef (go.ArrayType n elem_type) (l, "n" -⟨go.int⟩ #(W64 1)) in
                 let: "elem_val" := GoLoad elem_type "elem_addr" in
                 ArraySet ("array_so_far", ("n" -⟨go.int⟩ #(W64 1), "elem_val"))
         ) #(W64 n)))

  store_array (n : Int) (elem_type : go.type) (l v : val) :
    ⟦GoStore (go.ArrayType n elem_type), (l, v)⟧ ⤳[internal_under]
    (List.foldl (fun str_so_far j =>
                gl(str_so_far ;;
                (let elem_addr := gl(IndexRef (go.ArrayType n elem_type) (l, #(W64 j)))
                 let elem_val := gl(Index (go.ArrayType n elem_type) (v, #(W64 n)))
                 gl(GoStore elem_type (elem_addr, elem_val)))))
             (#() : expr) ((List.range n.toNat).map (fun (i : Nat) => (i : Int)))) -- Rocq: seqZ 0 n

  index_ref_array (n : Int) (elem_type : go.type) (i : w64) (l : loc) {V : Type} [ZeroVal V]
    [TypeRepr elem_type V] :
    ⟦IndexRef (go.ArrayType n elem_type), (#l, #i)⟧ ⤳[under]
      (if sint.Z i < n then #(array_index_ref V (sint.Z i) l) else Panic "index out of range")

  index_array (n : Int) (elem_type : go.type) (i : w64) (V : Type) (a : array.t V n) :
    ⟦Index (go.ArrayType n elem_type), (#a, #i)⟧ ⤳[under]
      (match a.arr[sint.nat i]? with
       | some v => #v
       | none => Panic "index out of range")

  composite_literal_array (n : Int) (elem_type : go.type) (kvs : List keyed_element) :
    ⟦CompositeLiteral (go.ArrayType n elem_type), (LiteralValueV kvs)⟧ ⤳[under]
    (List.foldl (fun (cur_index, expr_so_far) ke =>
             match ke with
             | KeyedElement none (ElementExpression from_ e) =>
                 (cur_index + 1,
                  gl(ArraySet (expr_so_far, (#(W64 cur_index), Convert from_ elem_type e))))
             | KeyedElement none (ElementLiteralValue l) =>
                 (cur_index + 1,
                  gl(ArraySet (expr_so_far,
                    (#(W64 cur_index), CompositeLiteral elem_type (LiteralValue l)))))
             | KeyedElement (some (KeyInteger cur_index)) (ElementExpression from_ e) =>
                 (cur_index + 1,
                  gl(ArraySet (expr_so_far, (#(W64 cur_index), Convert from_ elem_type e))))
             | KeyedElement (some (KeyInteger cur_index)) (ElementLiteralValue l) =>
                 (cur_index + 1,
                  gl(ArraySet (expr_so_far,
                    (#(W64 cur_index), CompositeLiteral elem_type (LiteralValue l)))))
             | _ => (0, Panic "invalid array literal")
      ) ((0 : Int), gl(GoZeroVal (go.ArrayType n elem_type) #())) kvs).2

  slice_array_step (n : Int) (elem_type : go.type) (p : loc) (low high : w64) {V : Type}
    [ZeroVal V] [TypeRepr elem_type V] :
    ⟦Slice (go.ArrayType n elem_type), (#p, #low, #high)⟧ ⤳
       (if 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ n then
          #(slice.mk (array_index_ref V (sint.Z low) p)
              (high - low)
              (W64 n - low))
        else Panic "slice bounds out of range")

  full_slice_array_step_pure (n : Int) (elem_type : go.type) (p : loc) (low high max : w64)
    {V : Type} [ZeroVal V] [TypeRepr elem_type V] :
    ⟦FullSlice (go.ArrayType n elem_type), (#p, #low, #high, #max)⟧ ⤳
    (if 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ sint.Z max ∧ sint.Z max ≤ n then
       #(slice.mk (array_index_ref V (sint.Z low) p)
           (high - low) (max - low))
     else Panic "slice bounds out of range")

  /-- This requires that array_index_ref does not ever end up becoming null due
  to a negative Z offset. Instead, negative offsets should be thought of as
  clamped to 0. -/
  array_index_ref_null_inv (t : Type) (i : Int) (l : loc) :
    array_index_ref t i l = null → l = null

  array_index_ref_add (t : Type) (i j : Int) (l : loc) :
    array_index_ref t (i + j) l = array_index_ref t j (array_index_ref t i l)

  /-- For disk FFI proof. -/
  array_index_ref_add_loc_add (i : Int) (l : loc) :
    array_index_ref w8 i l = l +ₗ i

  into_val_inj_array (V : Type) (n : Int) [inj_V : go.IntoValInj V] :
    go.IntoValInj (array.t V n)

attribute [instance] ArraySemantics.array_set_step ArraySemantics.array_length_step
  ArraySemantics.equals_array ArraySemantics.type_repr_array ArraySemantics.alloc_array
  ArraySemantics.load_array ArraySemantics.store_array ArraySemantics.index_ref_array
  ArraySemantics.index_array ArraySemantics.composite_literal_array
  ArraySemantics.slice_array_step ArraySemantics.full_slice_array_step_pure
  ArraySemantics.into_val_inj_array
export ArraySemantics (array_set_step array_length_step equals_array type_repr_array alloc_array
  load_array store_array index_ref_array index_array composite_literal_array slice_array_step
  full_slice_array_step_pure array_index_ref_null_inv array_index_ref_add
  array_index_ref_add_loc_add into_val_inj_array)

end defs
end go

end Perennial
