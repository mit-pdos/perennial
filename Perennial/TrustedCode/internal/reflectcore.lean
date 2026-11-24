/-
Trusted code for `internal/reflectcore` (namespace `internal.reflectcore`, as the generated
package): the reflection primitives of the Go models of `reflect`
(`goose/model/overlay/internal/reflectcore/core.go`). The package exists only in the model overlay
(`Perennial/Code/internal/reflectcore.toml`: a whole-package model of a path the standard library
does not have). Each exported function is a primitive stub, one reflection instruction of
`GooseLang/Lang.lean` (`FuncResolveAt`, `ConvertAt`, `FieldRefAt`, `ArraySliceAt`, `EqNilAt`,
`PointerOfAt`, `TypeQuery`); its Go body is a placeholder. A `FuncResolveAt` stub instantiates
one of the generic helpers of `helpers.go`, which goose translates, at its argument's dynamic type.
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace internal.reflectcore
section code
variable [GooseExts] [GoGlobalContext]

/-- `TokOf(x)`: `tokOf[T](x)` for `x`'s dynamic type `T`. -/
def TokOf.impl : val :=
  λ: "x", (FuncResolveAt [go.Shape.self] go!"internal/reflectcore.tokOf" "x") "x"

/-- `Box(x)`: `box[T](x)` for `x`'s dynamic type `T`. -/
def Box.impl : val :=
  λ: "x", (FuncResolveAt [go.Shape.self] go!"internal/reflectcore.box" "x") "x"

/-- `Load(p)`: `load[T](p)` for `p`'s dynamic type `*T`. -/
def Load.impl : val :=
  λ: "p", (FuncResolveAt [go.Shape.deref go.Shape.self] go!"internal/reflectcore.load" "p") "p"

/-- `Alloc(t)`: `alloc[T](t)` for `t`'s dynamic type `*T`. -/
def Alloc.impl : val :=
  λ: "t", (FuncResolveAt [go.Shape.deref go.Shape.self] go!"internal/reflectcore.alloc" "t") "t"

/-- `PtrTok(t)`: `ptrTok[T](t)` for `t`'s dynamic type `*T`. -/
def PtrTok.impl : val :=
  λ: "t", (FuncResolveAt [go.Shape.deref go.Shape.self] go!"internal/reflectcore.ptrTok" "t") "t"

/-- `ConvertAt(x, t)`: the instruction `ConvertAt`. -/
def ConvertAt.impl : val :=
  λ: "x" "t", ConvertAt ("x", "t")

/-- `FieldRefAt(p, i)`: the instruction `FieldRefAt`. -/
def FieldRefAt.impl : val :=
  λ: "p" "i", FieldRefAt ("p", "i")

/-- `ArraySliceAt(p)`: the instruction `ArraySliceAt`. -/
def ArraySliceAt.impl : val :=
  λ: "p", ArraySliceAt "p"

/-- `EqNilAt(x)`: the instruction `EqNilAt`. -/
def EqNilAt.impl : val :=
  λ: "x", EqNilAt "x"

/-- `PointerOfAt(x)`: the instruction `PointerOfAt`. -/
def PointerOfAt.impl : val :=
  λ: "x", PointerOfAt "x"

/-- `TypeKind(t)`: the instruction `TypeQuery .kind`. -/
def TypeKind.impl : val :=
  λ: "t", TypeQuery go.TypeQ.kind ("t", #(W64 0))

/-- `TypeElem(t)`: the instruction `TypeQuery .elem`. -/
def TypeElem.impl : val :=
  λ: "t", TypeQuery go.TypeQ.elem ("t", #(W64 0))

/-- `TypeLen(t)`: the instruction `TypeQuery .len`. -/
def TypeLen.impl : val :=
  λ: "t", TypeQuery go.TypeQ.len ("t", #(W64 0))

/-- `TypeNumField(t)`: the instruction `TypeQuery .numField`. -/
def TypeNumField.impl : val :=
  λ: "t", TypeQuery go.TypeQ.numField ("t", #(W64 0))

/-- `TypeFieldType(t, i)`: the instruction `TypeQuery .fieldType`. -/
def TypeFieldType.impl : val :=
  λ: "t" "i", TypeQuery go.TypeQ.fieldType ("t", "i")

end code
end internal.reflectcore

end Perennial
