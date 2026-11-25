/-
`kindOf` and `typeQuery` (`Perennial/Golang/Defn/Reflect.lean`) on unnamed and predeclared types:
the rows reflect gives.
-/
module

public import Perennial.Golang.Theory.Reflect

@[expose] public section

namespace Perennial

section tests

-- Unfold the predeclared types, so that `kindOf` compares their names; `layoutModelled` of an
-- unnamed type is false (`NotLayoutModelled`'s instances).
attribute [local simp] go.kindOf List.find? go.bool go.int go.int8 go.int16 go.int32 go.int64
  go.uint go.uint8 go.uint16 go.uint32 go.uint64 go.uintptr go.float32 go.float64 go.complex64
  go.complex128 go.string «unsafe».Pointer go.NotLayoutModelled.not_layout_modelled
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [go.PreSemantics]

/-- No model changes `int`. -/
@[local simp] theorem layoutModelled_int : go.layoutModelled (go.Named go!"int" []) = false := by
  decide

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

/-- `int` reaches no type a model changes. -/
theorem not_reaches_int : ¬ go.ReachesLayoutModelled go.int := by
  have hu : underlying go.int = go.int := go.is_underlying
  intro h
  cases h with
  | self h => exact absurd h (by decide)
  | field hs _ _ => rw [hu] at hs; simp [go.int] at hs
  | elem hs _ => rw [hu] at hs; simp [go.int] at hs

example : go.typeQuery .arrayOf go.int 4 = some #(go.tok (go.ArrayType 4 go.int)) := by
  simp only [go.typeQuery]
  rw [if_neg (by simp)]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨not_reaches_int, by decide,
    .inr ⟨8, ⟨⟨8, .scalar _ _ .isPlainScalar_int⟩⟩, by decide⟩⟩)]

/-! ## Types a model changes (`go.layoutModelled`) are opaque

The minimal program of Upamanyu's rule (etcd-grove#40): `type S struct{ mu sync.Mutex; n int }`
with a redefined `Mutex`. Here the redefined `Mutex` is `internal/sync.Mutex` (the field of the real
`sync.Mutex`), whose Lean definition is trusted (`TrustedCode/internal/sync.lean`: underlying
`bool`, Go's is a struct) and which goose lists in `go.layoutModelledNames`. -/

/-- `internal/sync.Mutex`. -/
abbrev isyncMutex : go.GoType := go.Named go!"internal/sync.Mutex" []

example : go.layoutModelled isyncMutex = true := by decide
example : go.layoutModelled (go.Named go!"reflect.rtype" []) = true := by decide
example : go.layoutModelled (go.Named go!"internal/reflectlite.rtype" []) = true := by decide
example : go.layoutModelled (go.Named go!"sync.Mutex" []) = false := by decide

/-- The fields of `S`: `mu isync.Mutex; n int`. -/
abbrev sFields : List go.field_decl := [go.FieldDecl go!"mu" isyncMutex, go.FieldDecl go!"n" go.int]

/-- `Kind(S)`, `NumField(S)`, `Field(i).Name` and `Field(i).Type` answer as in Go, for a defined
`S` (not itself changed by a model) of underlying type `struct{ mu Mutex; n int }`. -/
example (S : go.GoType) [S ↓u go.StructType sFields] (hS : go.layoutModelled S = false) :
    go.typeQuery .kind S 0 = some #(W64 25) ∧
    go.typeQuery .numField S 0 = some #(W64 2) ∧
    go.typeQuery .fieldName S 0 = some #go!"mu" ∧
    go.typeQuery .fieldName S 1 = some #go!"n" ∧
    go.typeQuery .fieldType S 0 = some #(go.tok isyncMutex) ∧
    go.typeQuery .fieldType S 1 = some #(go.tok go.int) := by
  simp [go.typeQuery, go.is_underlying, hS, go.listAt, go.fieldNameOf, go.fieldDeclName,
    go.fieldDeclType, go.isBlankField]

/-- Every question about `Mutex` itself is stuck (none), except `identByName`, which reads only
its name. -/
example (q : go.TypeQ) (hq : q ≠ .identByName) (i : Int) : go.typeQuery q isyncMutex i = none := by
  unfold go.typeQuery
  rw [if_pos ⟨by decide, hq⟩]

example : go.typeQuery .identByName isyncMutex 0 = some #true := by
  simp [go.typeQuery, go.identByName]

/-- `arrayOf(S)` depends on `S`'s size, so on `Mutex`'s: stuck, at any length. -/
example (S : go.GoType) [S ↓u go.StructType sFields] (i : Int) :
    go.typeQuery .arrayOf S i = none := by
  have hr : go.ReachesLayoutModelled S :=
    .field (fd := go.FieldDecl go!"mu" isyncMutex) go.is_underlying (by simp)
      (.self (by decide))
  unfold go.typeQuery
  split
  · rfl
  · simp [hr]

/-- `TypeOf(reflect.TypeOf(0)).Kind()`: `TypeOf` of a `Type` gives the token of the model's
`rtype`, whose kind is stuck. -/
example : go.typeQuery .kind (go.Named go!"reflect.rtype" []) 0 = none := by
  unfold go.typeQuery
  rw [if_pos ⟨by decide, by decide⟩]

end tests

end Perennial
