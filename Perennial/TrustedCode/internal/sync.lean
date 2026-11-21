/-
Trusted model of `internal/sync`'s `Mutex` (namespace `internal.sync`, as the generated
package), the lock under the translated `sync.Mutex`
(`type Mutex struct { _ noCopy; mu isync.Mutex }`).

Go's `Mutex` is `struct { state int32; sema uint32 }`: a lock-free fast path
(`CompareAndSwapInt32(&m.state, 0, mutexLocked)`) and a slow path (`lockSlow`,
`unlockSlow`) that spins, tracks waiters, starvation and wakeups in `state` with plain
loads racing with the CASes, and parks on the runtime's semaphores. None of it is
translatable (the races, the runtime semaphores), so the model is a spin lock on a
`bool` (`Golang/Defn/Lock.lean`; `false` is unlocked): `Mutex`'s underlying type is
`bool`, and the zero `Mutex` is unlocked, as in Go. The model is more nondeterministic
than Go (no fairness, no starvation mode), and `Lock` may spin forever where Go parks;
the specs are partial correctness, so that loses nothing they promise.

`internal/sync` is an internal package: only the standard library can name
`isync.Mutex`, so no translated program has an `isync.Mutex{}` literal (which would be
stuck at `CompositeLiteral go.bool`); `sync.Mutex{}` is a literal of the translated
struct `sync.Mutex`, whose zero value holds an unlocked `isync.Mutex`.
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.Golang.Defn.Lock

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace internal.sync

section code
variable [GooseExts] [GoGlobalContext]

/-- See the module docstring: the model's state of a `Mutex` is whether it is locked. -/
@[reducible] def Mutex.underlying : go.GoType := go.bool

/-- Model of (internal/sync/mutex.go)
```go
func (m *Mutex) TryLock() bool {
	old := m.state
	if old&(mutexLocked|mutexStarving) != 0 {
		return false
	}
	if !atomic.CompareAndSwapInt32(&m.state, old, old|mutexLocked) {
		return false
	}
	...
	return true
}
```
as a compare-and-swap of `false` (unlocked) to `true`. -/
def Mutex.TryLock.impl : val :=
  λ: "m" <>, lock.trylock "m"

/-- Model of (internal/sync/mutex.go)
```go
func (m *Mutex) Lock() {
	if atomic.CompareAndSwapInt32(&m.state, 0, mutexLocked) {
		...
		return
	}
	m.lockSlow()
}
```
as a loop of compare-and-swaps of `false` to `true` (`lockSlow` spins and then parks on
the runtime semaphore until the mutex is unlocked; the model spins). -/
def Mutex.Lock.impl : val :=
  λ: "m" <>, lock.lock "m"

/-- Model of (internal/sync/mutex.go)
```go
func (m *Mutex) Unlock() {
	...
	new := atomic.AddInt32(&m.state, -mutexLocked)
	if new != 0 {
		m.unlockSlow(new)
	}
}

func (m *Mutex) unlockSlow(new int32) {
	if (new+mutexLocked)&mutexLocked == 0 {
		fatal("sync: unlock of unlocked mutex")
	}
	...
}
```
as a compare-and-swap of `true` to `false`, stuck when the mutex is not locked (Go's
`fatal` ends the program; `recover` cannot catch it). Waking a waiter is implicit: a
spinning `Lock` sees the `false`. -/
def Mutex.Unlock.impl : val :=
  λ: "m" <>, lock.unlock "m"

end code

/-- See `Mutex.underlying`. -/
abbrev Mutex := Bool

end internal.sync

end Perennial
