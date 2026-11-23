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

/-- `Stuck()`: no behaviour (a stuck `Panic`, which `recover` cannot catch), so a verified program
never reaches a call; a model calls it where it gives up Go's behaviour (it is less defined than
Go there, never more). The Go body panics. -/
def Stuck.impl : val :=
  λ: <>, Panic "gomodel.Stuck"

end code
end internal.gomodel

end Perennial
