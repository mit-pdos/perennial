/-
`kindOf` and `typeQuery` (`Perennial/Golang/Defn/Reflect.lean`) on unnamed and predeclared types:
the rows reflect gives.
-/
module

public import Perennial.Golang.Theory.Reflect

@[expose] public section

namespace Perennial

section tests

-- Unfold the predeclared types, so that `kindOf` compares their names.
attribute [local simp] go.kindOf List.find? go.bool go.int go.int8 go.int16 go.int32 go.int64
  go.uint go.uint8 go.uint16 go.uint32 go.uint64 go.uintptr go.float32 go.float64 go.complex64
  go.complex128 go.string «unsafe».Pointer
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [go.PreSemantics]

example : go.kindOf go.bool = some 1 := by simp
example : go.kindOf go.int = some 2 := by simp
example : go.kindOf go.uint8 = some 8 := by simp
example : go.kindOf go.string = some 24 := by simp
example : go.kindOf «unsafe».Pointer = some 26 := by simp
example (e : go.GoType) : go.kindOf (go.SliceType e) = some 23 := rfl
example : go.kindOf go.error = some 20 := rfl
example : go.kindOf (go.UntypedType go!"int") = none := by simp

example : go.typeQuery .kind go.int 0 = some #(W64 2) := by
  rw [go.typeQuery, go.is_underlying (t := go.int)]
  simp

example (e : go.GoType) : go.typeQuery .kind (go.PointerType e) 0 = some #(W64 22) := by
  simp [go.typeQuery, go.is_underlying]

example (k v : go.GoType) : go.typeQuery .elem (go.MapType k v) 0 = some #(go.tok v) := by
  simp [go.typeQuery, go.is_underlying]

example (k v : go.GoType) : go.typeQuery .key (go.MapType k v) 0 = some #(go.tok k) := by
  simp [go.typeQuery, go.is_underlying]

example (e : go.GoType) : go.typeQuery .len (go.ArrayType 3 e) 0 = some #(W64 3) := by
  simp [go.typeQuery, go.is_underlying]

example (e : go.GoType) :
    go.typeQuery .chanDir (go.ChannelType go.recvonly e) 0 = some #(W64 1) := by
  simp [go.typeQuery, go.is_underlying, go.chanDirOf]

/-- `struct { A int; _ int; T }`: field names `A`, `_`, `T`; `T` is embedded. -/
example (t : go.GoType) :
    let st := go.StructType [go.FieldDecl go!"A" go.int, go.FieldDecl go!"_#1" go.int,
      go.EmbeddedField go!"T" t]
    go.typeQuery .numField st 0 = some #(W64 3) ∧
    go.typeQuery .fieldName st 1 = some #go!"_" ∧
    go.typeQuery .fieldName st 2 = some #go!"T" ∧
    go.typeQuery .fieldType st 0 = some #(go.tok go.int) ∧
    go.typeQuery .fieldEmbedded st 2 = some #true ∧
    go.typeQuery .fieldName st 3 = none := by
  simp [go.typeQuery, go.is_underlying, go.listAt, go.fieldNameOf, go.isEmbeddedField,
    go.fieldDeclName, go.fieldDeclType, go.isBlankField]

/-- `func(int, ...string) bool`. -/
example :
    let ft := go.FunctionType (go.Signature [go.int, go.SliceType go.string] true [go.bool])
    go.typeQuery .numIn ft 0 = some #(W64 2) ∧
    go.typeQuery .inType ft 1 = some #(go.tok (go.SliceType go.string)) ∧
    go.typeQuery .numOut ft 0 = some #(W64 1) ∧
    go.typeQuery .variadic ft 0 = some #true := by
  simp [go.typeQuery, go.is_underlying, go.listAt]

example : go.typeQuery .numTypeArgs go.int 0 = some #(W64 0) := by
  simp [go.typeQuery, go.int]

example (e : go.GoType) : go.typeQuery .name (go.SliceType e) 0 = none := by
  simp [go.typeQuery]

example : go.typeQuery .arrayOf go.int 4 = some #(go.tok (go.ArrayType 4 go.int)) := by
  simp only [go.typeQuery]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide,
    .inr ⟨8, ⟨⟨8, .scalar _ _ .isPlainScalar_int⟩⟩, by decide⟩⟩)]

end tests

end Perennial
