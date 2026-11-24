// The Go model of internal/sync's Mutex methods and of fatal
// (Perennial/Code/internal/sync.toml, [model]), spliced into mutex.go and
// runtime.go in place of the real declarations. The type Mutex is the real
// one, translated.

package sync

import (
	"internal/gomodel"
	"sync/atomic"
)

// MODEL: Go's Lock is a compare-and-swap of state from 0 to mutexLocked, and
// on failure lockSlow, which spins and parks on the runtime's semaphore
// (runtime_SemacquireMutex, runtime_canSpin, runtime_doSpin,
// runtime_nanotime, all without a Go body) and records waiters, wakeups and
// starvation in state, read with plain loads that race with the
// compare-and-swaps. Goose translates lockSlow, but the hooks have no body and
// the racy reads are outside what the sequentially consistent semantics
// models; and the protocol in state is shared with TryLock and Unlock, so
// they are replaced together. The model keeps state at 0 (unlocked) or
// mutexLocked and spins on the fast path's compare-and-swap until it
// succeeds: Lock returns exactly when it takes the mutex, as in Go; a
// spinning model goroutine where Go's parks is a schedule with the same
// results (the model has no fairness and no starvation mode, which only
// order waiters). A goroutine that never gets the mutex spins forever where
// Go's parks forever: spinning for parking is partial correctness, and Go's
// deadlock detector (a global deadlock becomes the fatal throw "all
// goroutines are asleep") is not modelled (docs/KNOWN_LIMITATIONS.md).
func (m *Mutex) Lock() {
	for !atomic.CompareAndSwapInt32(&m.state, 0, mutexLocked) {
	}
}

// MODEL: Go's TryLock returns false if state is locked or starving, or if its
// compare-and-swap of state to locked loses to a concurrent change, else
// true. The model's state has no starvation bit and no waiters, so where Go
// fails on an unlocked mutex (starvation mode, or a waiter changing state),
// the model fails by an arbitrary choice (gomodel.Choose); otherwise it is the
// compare-and-swap of 0 to mutexLocked. It thus returns false in every case
// Go does, and true only when it took the mutex, as in Go.
func (m *Mutex) TryLock() bool {
	if gomodel.Choose() {
		return false
	}
	return atomic.CompareAndSwapInt32(&m.state, 0, mutexLocked)
}

// MODEL: Go's Unlock subtracts mutexLocked from state and, if waiters remain,
// wakes one (unlockSlow, through runtime_Semrelease); on an unlocked mutex it
// calls fatal("sync: unlock of unlocked mutex"). The model's state has no
// waiters (a spinning Lock sees the 0), so Unlock is the compare-and-swap of
// mutexLocked to 0, and fatal where it fails, that is where the mutex is not
// locked.
func (m *Mutex) Unlock() {
	if !atomic.CompareAndSwapInt32(&m.state, mutexLocked, 0) {
		fatal("sync: unlock of unlocked mutex")
	}
}

// MODEL: Go's fatal (a runtime push linkname, no Go body) prints the message
// and ends the program, and recover cannot catch it. The model has no
// behaviour there (gomodel.Stuck): a verified program never calls it.
func fatal(string) {
	gomodel.Stuck()
}
