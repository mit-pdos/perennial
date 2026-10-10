/-
Semantics of Go arrays.
-/
module

public import Perennial.Golang.Defn.Predeclared
public import Perennial.Golang.Defn.Layout
public import Perennial.Golang.Defn.Loop

@[expose] public section

namespace Perennial

namespace go
section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

class ArraySemantics [GoSemanticsFunctions] : Prop where
  array_set_step (V : Type) (n : Int) (vs : GoArray V n) (i : w64) (v : V) :
    ⟦ArraySet, (#vs, (#i, #v))⟧ ⤳
    #(array.mk n (vs.arr.set (sint.nat i) v))

  array_length_step (vs : List val) :
    ⟦ArrayLength, (ArrayV vs)⟧ ⤳
    (if vs.length < 2 ^ 63 then #(W64 vs.length) else AngelicExit #())

  equals_array (n : Int) (t : go.GoType) [H : ⟦CheckComparable t, #()⟧ ⤳[under] #()] :
    ⟦CheckComparable (go.ArrayType n t), #()⟧ ⤳[under] #()

  type_repr_array (ty : go.GoType) (V : Type) (n : Int) [ZeroVal V] [TypeRepr ty V] :
    go.TypeReprUnderlying (go.ArrayType n ty) (GoArray V n)

  /-- An array is allocated as one block of `n` elements (`AllocN`), into which the value is
  stored. A size past the address space is not allocated (`AngelicExit`). -/
  alloc_array (n : Int) (elem : go.GoType) (v : val) {V : Type} [ZeroVal V] [TypeRepr elem V] :
    ⟦GoAlloc (go.ArrayType n elem), v⟧ ⤳[internalUnder]
      (if 0 ≤ n ∧ n * typeSize V < 2^63 then
        (Let "l" (AllocN (Val (LitV (LitInt (W64 (n * typeSize V))))) (Val #()))
          gl(GoStore (go.ArrayType n elem) ("l", v) ;; "l") : Expr)
       else gl(AngelicExit #()))

  load_array (n : Int) (elem_type : go.GoType) (l : val) :
    ⟦GoLoad (go.ArrayType n elem_type), l⟧ ⤳[internalUnder]
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

  /-- Stores element `j` of `#v` at index `j`. A value `#v` whose length is not
  `n` (possible, `GoArray V n` does not enforce it) or an `n` past the `w64`
  index range cannot satisfy `l ↦ v`, so those cases are `AngelicExit`, as in
  `load_array`. -/
  store_array (n : Int) (elem_type : go.GoType) (l : val) {V : Type} (v : GoArray V n) :
    ⟦GoStore (go.ArrayType n elem_type), (l, #v)⟧ ⤳[internalUnder]
    (if ¬(0 ≤ n ∧ n < 2^63-1 ∧ (v.arr.length : Int) = n) then
      gl(AngelicExit #())
    else
    List.foldl (fun str_so_far j =>
                gl(str_so_far ;;
                (let elem_addr := gl(IndexRef (go.ArrayType n elem_type) (l, #(W64 j)))
                 let elem_val := gl(Index (go.ArrayType n elem_type) (#v, #(W64 j)))
                 gl(GoStore elem_type (elem_addr, elem_val)))))
             (#() : Expr) ((List.range n.toNat).map (fun (i : Nat) => (i : Int))))

  index_ref_array (n : Int) (elem_type : go.GoType) (i : w64) (l : Loc) {V : Type} [ZeroVal V]
    [TypeRepr elem_type V] :
    ⟦IndexRef (go.ArrayType n elem_type), (#l, #i)⟧ ⤳[under]
      (if sint.Z i < n then #(arrayIndexRef V (sint.Z i) l) else Panic "index out of range")

  index_array (n : Int) (elem_type : go.GoType) (i : w64) (V : Type) (a : GoArray V n) :
    ⟦Index (go.ArrayType n elem_type), (#a, #i)⟧ ⤳[under]
      (match a.arr[sint.nat i]? with
       | some v => #v
       | none => Panic "index out of range")

  /-- `len` and `cap` of an array are both its length, which is part of its
  type rather than something stored alongside the elements. Go makes such a
  call a constant expression whenever the operand has no channel receives or
  non-constant calls, so Goose emits the length directly in that case and
  these rules cover only the remainder (e.g. `len(f())`); the operand is
  still evaluated, for its effects, and discarded. The guard matches
  `array_length_step`: an array whose length is not representable as a Go
  `int` cannot arise from a Go program. -/
  len_array {st : go.GoType} {n : Int} {elem_type : go.GoType} [st ↓u go.ArrayType n elem_type] :
    FuncUnfold go.len [st]
    (λ: <>, (if 0 ≤ n ∧ n < 2^63 then #(W64 n) else AngelicExit #()) : val)

  cap_array {st : go.GoType} {n : Int} {elem_type : go.GoType} [st ↓u go.ArrayType n elem_type] :
    FuncUnfold go.cap [st]
    (λ: <>, (if 0 ≤ n ∧ n < 2^63 then #(W64 n) else AngelicExit #()) : val)

  composite_literal_array (n : Int) (elem_type : go.GoType) (kvs : List keyed_element) :
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

  slice_array_step (n : Int) (elem_type : go.GoType) (p : Loc) (low high : w64) {V : Type}
    [ZeroVal V] [TypeRepr elem_type V] :
    ⟦Slice (go.ArrayType n elem_type), (#p, #low, #high)⟧ ⤳
       (if 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ n then
          #(slice.mk (arrayIndexRef V (sint.Z low) p)
              (high - low)
              (W64 n - low))
        else Panic "slice bounds out of range")

  fullSlice_array_step_pure (n : Int) (elem_type : go.GoType) (p : Loc) (low high max : w64)
    {V : Type} [ZeroVal V] [TypeRepr elem_type V] :
    ⟦FullSlice (go.ArrayType n elem_type), (#p, #low, #high, #max)⟧ ⤳
    (if 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ sint.Z max ∧ sint.Z max ≤ n then
       #(slice.mk (arrayIndexRef V (sint.Z low) p)
           (high - low) (max - low))
     else Panic "slice bounds out of range")


  intoVal_inj_array (V : Type) (n : Int) [inj_V : go.IntoValInj V] :
    go.IntoValInj (GoArray V n)

attribute [instance] ArraySemantics.array_set_step ArraySemantics.array_length_step
  ArraySemantics.equals_array ArraySemantics.type_repr_array ArraySemantics.alloc_array
  ArraySemantics.load_array ArraySemantics.store_array ArraySemantics.index_ref_array
  ArraySemantics.index_array ArraySemantics.len_array ArraySemantics.cap_array
  ArraySemantics.composite_literal_array
  ArraySemantics.slice_array_step ArraySemantics.fullSlice_array_step_pure
  ArraySemantics.intoVal_inj_array
export ArraySemantics (array_set_step array_length_step equals_array type_repr_array alloc_array
  load_array store_array index_ref_array index_array len_array cap_array composite_literal_array
  slice_array_step
  fullSlice_array_step_pure intoVal_inj_array)

/-- An index never takes a non-null array to `null` (`arrayIndexRef` stays in the block). -/
theorem arrayIndexRef_null_inv [GoSemanticsFunctions] (t : Type) (i : Int) (l : Loc) :
    arrayIndexRef t i l = null → l = null := by
  unfold arrayIndexRef
  split
  · exact id
  · intro h
    have := congrArg Loc.locCar h
    simp [Loc.add, null] at this
    contradiction

theorem arrayIndexRef_add [GoSemanticsFunctions] (t : Type) (i j : Int) (l : Loc) :
    arrayIndexRef t (i + j) l = arrayIndexRef t j (arrayIndexRef t i l) := by
  unfold arrayIndexRef
  split
  · simp [*]
  · rename_i h
    simp only [Loc.add, h, if_false]
    congr 1
    simp only [Int.add_mul]; omega

/-- Bytes are consecutive cells (for the disk FFI proof), in a real block. -/
theorem arrayIndexRef_add_loc_add [GoSemanticsFunctions] [LayoutSemantics] (i : Int) (l : Loc)
    (h : l.locCar ≠ 0) : arrayIndexRef w8 i l = l +ₗ i := by
  rw [arrayIndexRef_of_car _ _ _ h, typeSize_w8, Int.mul_one]

end defs
end go

/-! ## Range loops over arrays

`for k, v := range x` over an array `x : [n]T` takes the elements of the value
of `x` when the loop starts (an array is a value, so later writes to `x` are not
seen); over a pointer `p : *[n]T` it reads element `k` of `*p` at iteration `k`.
Without a value variable, the loop does not read the elements (`forRangeIndex`).
The key is an `int`, from `0` to `n - 1`. As for `slice.forRange`, `body` takes
the key (and the value) and returns the outcome of the loop body (`do:`,
`break:`, `continue:` or `return:`). -/

namespace array
section goose_lang
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]

/-- `for k := range x`, `x` an array (or a pointer to one) of length `n`. -/
def forRangeIndex (n : Int) : val :=
  λ: "body",
  let: "i" := GoAlloc go.int #(W64 0) in
  for: (λ: <>, (![go.int] "i") <⟨go.int⟩ #(W64 n)) ;
                      (λ: <>, "i" <-[go.int] (![go.int] "i") +⟨go.int⟩ #(W64 1)) :=
    (λ: <>, "body" (![go.int] "i"))

/-- `for k, v := range a`, `a : [n]elem_type` (an array value). -/
def forRange (n : Int) (elem_type : go.GoType) : val :=
  λ: "a" "body", (forRangeIndex n) (λ: "k", "body" "k" (Index (go.ArrayType n elem_type) ("a", "k")))

/-- `for k, v := range p`, `p : *[n]elem_type`. -/
def forRangePtr (n : Int) (elem_type : go.GoType) : val :=
  λ: "p" "body", (forRangeIndex n)
    (λ: "k", "body" "k" (![elem_type] (IndexRef (go.ArrayType n elem_type) ("p", "k"))))

end goose_lang
end array

attribute [irreducible] array.forRangeIndex array.forRange array.forRangePtr

end Perennial
