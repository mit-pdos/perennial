/-
Trusted code for `sync` (namespace `sync`, as the generated package): the one primitive stub of
its Go model (`goose/model/overlay/sync`, `Perennial/Code/sync.toml`). Everything else the model
replaces (the runtime hooks, `copyChecker`, `Pool.Get`/`Put`) is translated Go.
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace sync
section code
variable [GooseExts] [GoGlobalContext]

/-- `poolModelAt(l)`, Go's `(*poolModel)(l)`: the identity on the address. The semantics converts an
`unsafe.Pointer` only to a pointer to a plain type (`Golang/Defn/Plain.lean`), and `poolModel` (a
`Mutex` and a slice) is not one. The model calls it only on a non-nil value of a `Pool`'s field
`local`, which is unexported and which, with `Get` and `Put` modelled, only the model's
`poolModelOf` writes, always with a `*poolModel` converted to `unsafe.Pointer` (the identity,
`convert_pointer_to_unsafe`): so the conversion back is the identity, in Go as here. -/
def poolModelAt.impl : val :=
  λ: "l", "l"

/-- `copyChecker` is a `uintptr` (sync/cond.go:
`type copyChecker uintptr`) that is only ever `0` or its own address
`uintptr(unsafe.Pointer(c))`. goose supports neither `uintptr` nor
pointer-to-integer conversions, so it is modeled as an `unsafe.Pointer` (a
`loc`): `0` is `null`, and `uintptr(unsafe.Pointer(c))` is `c` itself. -/
@[reducible] def copyChecker.underlying : go.GoType := «unsafe».Pointer

/-- Model of (sync/cond.go)
```
func (c *copyChecker) check() {
	if uintptr(*c) != uintptr(unsafe.Pointer(c)) &&
		!atomic.CompareAndSwapUintptr((*uintptr)(c), 0, uintptr(unsafe.Pointer(c))) &&
		uintptr(*c) != uintptr(unsafe.Pointer(c)) {
		panic("sync.Cond is copied")
	}
}
```
The two reads of `*c` are plain loads in Go (racing with the CAS; the sync
package is exempt from the race detector); they are modeled as (atomic)
`Load`s. -/
def copyChecker.check.impl : val :=
  λ: "c" <>,
    if: Load "c" =⟨«unsafe».Pointer⟩ "c" then #()
    else if: Snd (CmpXchg "c" #null "c") then #()
    else if: Load "c" =⟨«unsafe».Pointer⟩ "c" then #()
    else Panic "sync.Cond is copied"

end code
/-- See `copyChecker.underlying`. -/
abbrev copyChecker := Loc

end sync

end Perennial
