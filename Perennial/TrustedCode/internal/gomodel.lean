/-
Trusted code for `internal/gomodel` (namespace `internal.gomodel`, as the generated package): the
choice and stuck points of the Go models of standard-library packages
(`goose/model/overlay/internal/gomodel/gomodel.go`). The package exists only in the model overlay
(`Perennial/Code/internal/gomodel.toml`: a whole-package model of a path the standard library does
not have), and each of its functions is a primitive stub: its Go body serves gc builds and
differential tests only, and its model is here.
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace internal.gomodel
section code
variable [GooseExts] [GoGlobalContext]

/-- `Choose()`: an arbitrary boolean. A model calls it where Go's behaviour depends on what the
model does not track (a scheduler decision, the runtime's state), so the model has the behaviours
of both sides; the Go body returns `false`. -/
def Choose.impl : val :=
  λ: <>, ArbitraryInt =⟨go.uint64⟩ #(W64 0)

/-- `ChooseUint64()`: an arbitrary `uint64`; the Go body returns 0. -/
def ChooseUint64.impl : val :=
  λ: <>, ArbitraryInt

/-- `Stuck()`: no behaviour. A model calls it where it does not model Go's behaviour, so the model
is less defined than Go there, never more. It is the stuck `Panic "not modelled"` (`PanicOp`, as a
nil dereference is): `recover` cannot catch it and no WP rule steps it, so a verified program never
reaches a call. A model that blocked forever instead (`select {}`, the Go body) would be unsound
here: `chan.wp_select_blocking []` has precondition `True`, which proves anything after it. This is
the shared stuck point of every Go model: a model outside the standard library, which cannot import
`internal/gomodel`, declares its own primitive stub (Go body `select {}`) whose `.impl` is this
definition. -/
def Stuck.impl : val :=
  λ: <>, Panic "not modelled"

end code
end internal.gomodel

end Perennial
