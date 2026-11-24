/-
Trusted definitions of `github.com/goose-lang/primitive`.

The definitions live in the namespace of the generated package
(`github_com.goose_lang.primitive`), where the generated code refers to them.
The named type `primitive.Mutex` is not defined here: the
generated code defines `github_com.goose_lang.primitive.Mutex`. Its model is the spin lock on a
boolean `lock.lock`/`lock.unlock` below (moved here unchanged from `Golang/Defn/Lock.lean`,
now that `internal/sync.Mutex` is a Go model and this is its only user). `Mutex` and `Assume` are
not a Go model overlay: the overlay cannot replace a file of a module under GOMODCACHE, where
goose finds `primitive`.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

/-! A spin lock on a boolean location (`false` is unlocked), the model of `primitive.Mutex`'s
`Lock` and `Unlock`. -/
section lockcode
variable [GooseExts] [GoGlobalContext]

namespace lock
set_option linter.iris.dupNamespace false in
def lock : val :=
  rec: "lock" "m" :=
    if: Snd (CmpXchg "m" #false #true) then
      #()
    else
      "lock" "m"

/-- Unlocks the lock; stuck if it is not locked, where Go's `Mutex.Unlock` ends the program
with `fatal("sync: unlock of unlocked mutex")` (`internal/sync/mutex.go`, `unlockSlow`),
which `recover` cannot catch. -/
def unlock : val :=
  λ: "m", if: Snd (CmpXchg "m" #true #false) then #()
    else Panic "sync: unlock of unlocked mutex"

end lock

end lockcode

attribute [irreducible] lock.lock lock.unlock

namespace github_com.goose_lang.primitive
section code
variable [GooseExts] [GoGlobalContext]

/-- `Assume c` goes into an endless loop if `c` does not hold, so proofs can assume that it holds.
Go's `Assume` panics there instead: this model does not have that behaviour (nor a deferred
`recover` catching the panic). It is intended: `Assume` is the library's explicit verification
assumption (the program's author asserts `c`), the one declaration of `primitive` whose model has
fewer behaviours than Go. -/
def Assume.impl : val :=
  λ: "cond", if: Var "cond" then #()
             else (rec: "loop" <> := Var "loop" #()) #()

def RandomUint64.impl : val := λ: <>, ArbitraryInt

/-! Prophecy variables. goose's `primitive` declares `NewProph() ProphId`,
`(ProphId) ResolveBool(bool)` and `(ProphId) ResolveU64(uint64)` as no-op stubs
(`proph.go`: `NewProph` returns `ProphId{}`, the resolves have empty bodies). goose
translates them, but the translation is the no-op: the functions exist to carry the
meaning of a prophecy variable, which has no runtime effect and which no Go code can
express. So they are trusted, modelled by GooseLang's prophecy primitives, which touch
only ghost state; the observable behaviour (no effect, a value of `ProphId`) is the
stub's. -/

/-- `NewProph()` creates a prophecy variable. -/
def NewProph.impl : val := λ: <>, NewProph

/-- `p.ResolveBool(b)` resolves the prophecy `p` with the value `#b`. -/
def ProphId.ResolveBool.impl : val := λ: "p" "b", ResolveProph (Var "p") (Var "b")

/-- `p.ResolveU64(x)` resolves the prophecy `p` with the value `#x`. -/
def ProphId.ResolveU64.impl : val := λ: "p" "x", ResolveProph (Var "p") (Var "x")

@[reducible] def Mutex.underlying : go.GoType := go.bool

def Mutex.Lock.impl : val :=
  λ: "m" <>, lock.lock "m"

def Mutex.Unlock.impl : val :=
  λ: "m" <>, lock.unlock "m"

@[reducible] def ProphId.underlying : go.GoType := go.prophId

end code

abbrev Mutex := Bool

abbrev ProphId := Perennial.proph_id

end github_com.goose_lang.primitive

end Perennial
