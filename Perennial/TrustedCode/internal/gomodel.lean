/-
Trusted code for `internal/gomodel` (namespace `internal.gomodel`, as the generated package): the
choice, stuck and read-lock points of the Go models of standard-library packages
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

/-- `StartRead[T](p)`: from here on the heap cell at `p` is read-only. It leaves a reader on that
cell for good (`StartRead` with no `FinishRead`), so later loads of it still step and stores to it
are stuck (a store, a swap or a successful compare-and-swap steps only at a cell with no reader).
A model calls it where a later write would make the model behave other than Go (the bytes that
`strings.Builder.String`'s result shares in Go, and `strings.Builder.addr`, which gc may leave
stale): that write is stuck in the model, which is thus less defined than Go there, never more.
Only the one cell at `p` is marked, whatever `T`; at a `p` with no cell (nil) the call is stuck,
again only less defined. The Go body does nothing. -/
def StartRead.impl (_T : go.GoType) : val :=
  λ: "p", StartRead "p" ;; #()

end code
end internal.gomodel

end Perennial
