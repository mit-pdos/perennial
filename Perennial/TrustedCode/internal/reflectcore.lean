/-
Trusted code for `internal/reflectcore` (namespace `internal.reflectcore`, as the generated
package): the reflection primitives of the Go models of `reflect`
(`goose/model/overlay/internal/reflectcore/core.go`). The package exists only in the model overlay
(`Perennial/Code/internal/reflectcore.toml`: a whole-package model of a path the standard library
does not have). Each exported function is a primitive stub, one operation of the reflection
extension (`ExternalOp reflectExtName o`, `Perennial/GooseLang/Ext/Reflect/Impl.lean`:
`FuncResolveAt`, `ConvertAt`, `FieldRefAt`, `ArraySliceAt`, `EqNilAt`, `TypeQuery.<q>`); its Go
body is a placeholder. A `FuncResolveAt` stub instantiates one of the generic helpers of
`helpers.go`, which goose translates, at its argument's dynamic type.
-/
module

public import Perennial.Golang.Defn
public import Perennial.GooseLang.Ext.Reflect.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace internal.reflectcore
section code
variable [GooseExts] [GoGlobalContext]

/-- `TokOf(x)`: `tokOf[T](x)` for `x`'s dynamic type `T`. -/
def TokOf.impl : val :=
  λ: "x", (ExternalOp reflectExtName "FuncResolveAt" (Val (go.funcAtArg go!"internal/reflectcore.tokOf" [.self]), "x")) "x"

/-- `Box(x)`: `box[T](x)` for `x`'s dynamic type `T`. -/
def Box.impl : val :=
  λ: "x", (ExternalOp reflectExtName "FuncResolveAt" (Val (go.funcAtArg go!"internal/reflectcore.box" [.self]), "x")) "x"

/-- `Load(p)`: `load[T](p)` for `p`'s dynamic type `*T`. -/
def Load.impl : val :=
  λ: "p", (ExternalOp reflectExtName "FuncResolveAt" (Val (go.funcAtArg go!"internal/reflectcore.load" [.deref .self]), "p")) "p"

/-- `Alloc(t)`: `alloc[T](t)` for `t`'s dynamic type `*T`. -/
def Alloc.impl : val :=
  λ: "t", (ExternalOp reflectExtName "FuncResolveAt" (Val (go.funcAtArg go!"internal/reflectcore.alloc" [.deref .self]), "t")) "t"

/-- `PtrTok(t)`: `ptrTok[T](t)` for `t`'s dynamic type `*T`. -/
def PtrTok.impl : val :=
  λ: "t", (ExternalOp reflectExtName "FuncResolveAt" (Val (go.funcAtArg go!"internal/reflectcore.ptrTok" [.deref .self]), "t")) "t"

/-- `Store(p, x)`: `store[T](p, x)` for `p`'s dynamic type `*T`. -/
def Store.impl : val :=
  λ: "p" "x", (ExternalOp reflectExtName "FuncResolveAt" (Val (go.funcAtArg go!"internal/reflectcore.store" [.deref .self]), "p")) "p" "x"

/-- `AssertOk(t, x)`: `assertOk[T](x)` for `t`'s dynamic type `*T`. -/
def AssertOk.impl : val :=
  λ: "t" "x", (ExternalOp reflectExtName "FuncResolveAt" (Val (go.funcAtArg go!"internal/reflectcore.assertOk" [.deref .self]), "t")) "x"

/-- `ConvertAt(x, t)`: the operation `ConvertAt`. -/
def ConvertAt.impl : val :=
  λ: "x" "t", ExternalOp reflectExtName "ConvertAt" ("x", "t")

/-- `FieldRefAt(p, i)`: the operation `FieldRefAt`. -/
def FieldRefAt.impl : val :=
  λ: "p" "i", ExternalOp reflectExtName "FieldRefAt" ("p", "i")

/-- `ArraySliceAt(p)`: the operation `ArraySliceAt`. -/
def ArraySliceAt.impl : val :=
  λ: "p", ExternalOp reflectExtName "ArraySliceAt" "p"

/-- `EqNilAt(x)`: the operation `EqNilAt`. -/
def EqNilAt.impl : val :=
  λ: "x", ExternalOp reflectExtName "EqNilAt" "x"

/-- `TypeKind(t)`: the operation `TypeQuery.kind`. -/
def TypeKind.impl : val :=
  λ: "t", ExternalOp reflectExtName "TypeQuery.kind" ("t", #(W64 0))

/-- `TypeElem(t)`: the operation `TypeQuery.elem`. -/
def TypeElem.impl : val :=
  λ: "t", ExternalOp reflectExtName "TypeQuery.elem" ("t", #(W64 0))

/-- `TypeLen(t)`: the operation `TypeQuery.len`. -/
def TypeLen.impl : val :=
  λ: "t", ExternalOp reflectExtName "TypeQuery.len" ("t", #(W64 0))

/-- `TypeNumField(t)`: the operation `TypeQuery.numField`. -/
def TypeNumField.impl : val :=
  λ: "t", ExternalOp reflectExtName "TypeQuery.numField" ("t", #(W64 0))

/-- `TypeFieldType(t, i)`: the operation `TypeQuery.fieldType`. -/
def TypeFieldType.impl : val :=
  λ: "t" "i", ExternalOp reflectExtName "TypeQuery.fieldType" ("t", "i")

/-- `TypeUnderlying(t)`: the operation `TypeQuery.underlying`. -/
def TypeUnderlying.impl : val :=
  λ: "t", ExternalOp reflectExtName "TypeQuery.underlying" ("t", #(W64 0))

/-- `TypeIdentByName(t)`: the operation `TypeQuery.identByName`. -/
def TypeIdentByName.impl : val :=
  λ: "t", ExternalOp reflectExtName "TypeQuery.identByName" ("t", #(W64 0))

end code
end internal.reflectcore

end Perennial
