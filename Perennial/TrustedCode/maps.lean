/-
Trusted code for the Go `maps` package, in namespace `maps` (as the generated package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace maps
section code
variable [GooseExts] [GoGlobalContext]

/-- `clone(m any) any` (maps/maps.go), a `go:linkname` to the runtime (`runtime/map.go`'s
`maps_clone`, which calls `internal/runtime/maps`'s `clone`; no Go body, so goose rejects it): a
new map holding the entries of the map in `m`, returned in an interface of `m`'s dynamic type. Its
one caller, `Clone`, passes a non-nil map and asserts the result back to `M`. The model is the
semantics' `InternalMapClone` (`internal_map_clone_step`), stuck on anything but an interface
holding a map. Go evidence: `goose/model/maps/clone_test.go`. -/
noncomputable def clone.impl : val :=
  (LamV "m" (App (Val (GoInstruction InternalMapClone)) (Var "m")))

end code
end maps

end Perennial
