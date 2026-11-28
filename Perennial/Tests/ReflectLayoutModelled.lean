/-
The shapes the reflect and reflectlite models compute (`reflect.directIfaceN`, `reflect.zeroSizeN`,
`Perennial/Proof/internal/reflectcore/Base.lean`) recurse through questions on the component types,
so they are stuck (none) exactly at a type a model changes (`go.layoutModelled`). The minimal
program of Upamanyu's rule (etcd-grove#40): `type S struct{ mu sync.Mutex; n int }` with a
redefined `Mutex` (here `sync.copyChecker`, which `sync`'s Go model redefines).
-/
module

public import Perennial.Proof.internal.reflectcore.Base

@[expose] public section

namespace Perennial

section tests
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [go.PreSemantics]

/-- `sync.copyChecker`. -/
abbrev modelledTy' : go.GoType := go.Named go!"sync.copyChecker" []

/-- The fields of `S`: `mu sync.copyChecker; n int`. -/
abbrev sFields' : List go.field_decl :=
  [go.FieldDecl go!"mu" modelledTy', go.FieldDecl go!"n" go.int]

/-- `isDirectIface(S)` (so `ValueOf(s)`) asks only about `S`'s last field, `int`: `false`, as gc
says, without a question about `Mutex`. -/
example (S : go.GoType) [S ↓u go.StructType sFields'] [go.NotLayoutModelled S] :
    reflect.directIfaceN 2 S = some false := by
  have hu : underlying go.int = go.int := go.is_underlying
  exact reflect.directIfaceN_struct_last (f := go.FieldDecl go!"n" go.int) (k := 2) 0 (by decide) rfl hu
    (by decide) (by simp [go.kindOf, List.find?, go.bool, go.int]) (by decide) (by decide) (by decide)

/-- `isZeroSize(S)` recurses into `Mutex`: stuck (none), at any fuel. -/
example (S : go.GoType) [S ↓u go.StructType sFields'] [hS : go.NotLayoutModelled S] (n : Nat) :
    reflect.zeroSizeN n S = none := by
  have hu : underlying S = go.StructType sFields' := go.is_underlying
  cases n with
  | zero => rfl
  | succ n =>
    simp only [reflect.zeroSizeN, hS.not_layout_modelled, hu, Bool.false_eq_true, ↓reduceIte]
    rw [if_pos (by decide)]
    simp [go.fieldDeclType, reflect.allTrue,
      reflect.zeroSizeN_layoutModelled n (t := modelledTy') (by decide)]

/-- `isDirectIface` of a struct whose last field is a `Mutex` is stuck. -/
example (S : go.GoType) [S ↓u go.StructType [go.FieldDecl go!"n" go.int,
    go.FieldDecl go!"mu" modelledTy']] [hS : go.NotLayoutModelled S] (n : Nat) :
    reflect.directIfaceN n S = none := by
  have hu : underlying S = go.StructType [go.FieldDecl go!"n" go.int,
      go.FieldDecl go!"mu" modelledTy'] := go.is_underlying
  cases n with
  | zero => rfl
  | succ n =>
    simp only [reflect.directIfaceN, hS.not_layout_modelled, hu, Bool.false_eq_true, ↓reduceIte]
    rw [if_pos (by decide)]
    simp [go.fieldDeclType, reflect.directIfaceN_layoutModelled n (t := modelledTy') (by decide)]

end tests

end Perennial
