/-
Trusted code for `reflect`, in namespace `reflect` (as the generated package): the
initializers of the package variables that hold runtime type descriptors.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace reflect
section code
variable [GooseExts] [GoGlobalContext]

/-- The initializer of `stringType` (`reflect/map.go`):

```go
var stringType = rtypeOf("")
```

The model skips it (`go.skipInit`): `stringType` is not allocated. Its value is the runtime type
descriptor of `string`, which the semantics cannot represent: `rtypeOf` is `abi.TypeOf`, which
reads the descriptor out of an interface's memory through `unsafe` (`internal/abi/type.go`).
Go's initializer reads a static descriptor and allocates nothing the program can see, so it
cannot panic and has no other effect. (Translated, `rtypeOf` calls `abi.TypeOf`, whose body
`*(*EmptyInterface)(unsafe.Pointer(&a))` loads an `any` cell as an `abi.EmptyInterface`: a layout
reinterpretation, stuck in the semantics.) Its readers (`Value.MapIndex`, `Value.SetMapIndex`) are
not translated; a translated reader could not load the variable (nothing gives a points-to for
it). -/
def stringType.init : val := go.skipInit

/-- The initializer of `bytesType` (`reflect/value.go`):

```go
var bytesType = rtypeOf(([]byte)(nil))
```

The model skips it (`go.skipInit`): `bytesType` is not allocated, for the reasons of
`stringType.init` (the descriptor of `[]byte`). Its reader (`Value.Bytes`) is not translated. -/
def bytesType.init : val := go.skipInit

/-- The initializer of `uint8Type` (`reflect/value.go`):

```go
var uint8Type = rtypeOf(uint8(0))
```

The model skips it (`go.skipInit`): `uint8Type` is not allocated, for the reasons of
`stringType.init` (the descriptor of `uint8`). Its reader (`Value.Index` of a string) is not
translated. -/
def uint8Type.init : val := go.skipInit

end code
end reflect

end Perennial
