// The Go model of sync's runtime hooks (Perennial/Code/sync.toml, [model]),
// spliced into runtime.go in place of the real declarations. Each real one is
// a function with no Go body that the runtime defines by a push linkname
// (runtime/sema.go); the overlay blanks those directives, so that gc links
// these bodies instead.

package sync

import (
	"sync/atomic"
)

// MODEL: Go's runtime_Semacquire (runtime/sema.go, semacquire1) waits until
// *s > 0 and decrements it, trying first
//
//	func cansemacquire(addr *uint32) bool {
//		for {
//			v := atomic.Load(addr)
//			if v == 0 {
//				return false
//			}
//			if atomic.Cas(addr, v, v-1) {
//				return true
//			}
//		}
//	}
//
// and, while that fails, parking on a queue that runtime_Semrelease wakes. The
// model is cansemacquire's loop, retried until it succeeds: it returns exactly
// when it has decremented a positive *s, as Go's does; a model goroutine
// spinning where Go's parks is a schedule with the same results (the queue
// only orders the waiters). A goroutine that never acquires spins forever
// where Go's parks forever: spinning for parking is partial correctness, and
// Go's deadlock detector (a global deadlock becomes the fatal throw "all
// goroutines are asleep") is not modelled (docs/KNOWN_LIMITATIONS.md).
func runtime_Semacquire(s *uint32) {
	for {
		v := atomic.LoadUint32(s)
		if v == 0 {
			continue
		}
		if atomic.CompareAndSwapUint32(s, v, v-1) {
			return
		}
	}
}

// MODEL: as runtime_Semacquire: Go's differs only in the reason it reports
// for a parked goroutine and in synctest's durable blocking, which the model
// does not observe.
func runtime_SemacquireWaitGroup(s *uint32, synctestDurable bool) {
	runtime_Semacquire(s)
}

// MODEL: as runtime_Semacquire: lifo and skipframes only order the waiters
// and select the profiled stack frames.
func runtime_SemacquireRWMutexR(s *uint32, lifo bool, skipframes int) {
	runtime_Semacquire(s)
}

// MODEL: as runtime_Semacquire (see runtime_SemacquireRWMutexR).
func runtime_SemacquireRWMutex(s *uint32, lifo bool, skipframes int) {
	runtime_Semacquire(s)
}

// MODEL: Go's runtime_Semrelease (semrelease1) atomically increments *s and
// wakes a waiter if there is one (handing it the count directly if handoff);
// the model's waiters spin, so it is the increment.
func runtime_Semrelease(s *uint32, handoff bool, skipframes int) {
	atomic.AddUint32(s, 1)
}

// MODEL: Go's runtime_notifyListAdd (runtime/sema.go, notifyListAdd) is
//
//	return l.wait.Add(1) - 1
//
// the next ticket of the list, taken atomically; the model is the same over
// sync/atomic (wait is the runtime's atomic.Uint32, a uint32 in sync's copy of
// the type).
func runtime_notifyListAdd(l *notifyList) uint32 {
	return atomic.AddUint32(&l.wait, 1) - 1
}

// MODEL: Go's runtime_notifyListWait (notifyListWait) returns at once if
// ticket t has been notified, less(t, l.notify) with
//
//	func less(a, b uint32) bool {
//		return int32(a-b) < 0
//	}
//
// and otherwise parks until a notify call readies it, which the notify calls
// do exactly when they advance l.notify past t (NotifyOne readies the waiter
// whose ticket is the old l.notify, NotifyAll every waiter). The model spins
// on the same test, reading l.notify atomically: it returns exactly when Go's
// can. A goroutine that is never notified spins forever where Go's parks
// forever: spinning for parking is partial correctness, and Go's deadlock
// detector (a global deadlock becomes the fatal throw "all goroutines are
// asleep") is not modelled (docs/KNOWN_LIMITATIONS.md).
func runtime_notifyListWait(l *notifyList, t uint32) {
	for int32(t-atomic.LoadUint32(&l.notify)) >= 0 {
	}
}

// MODEL: Go's runtime_notifyListNotifyAll (notifyListNotifyAll) returns if
// l.wait == l.notify (no waiter), and otherwise, under the list's lock, sets
// l.notify to l.wait and readies every parked waiter. The model reads both and
// sets l.notify with a compare-and-swap, retried if l.notify changed in
// between: the store linearizes at the compare-and-swap, as Go's does under
// the lock (the lock only orders the notify calls, which the compare-and-swap
// also does). The waiters are readied by the new l.notify (see
// runtime_notifyListWait).
func runtime_notifyListNotifyAll(l *notifyList) {
	for {
		n := atomic.LoadUint32(&l.notify)
		w := atomic.LoadUint32(&l.wait)
		if n == w || atomic.CompareAndSwapUint32(&l.notify, n, w) {
			return
		}
	}
}

// MODEL: Go's runtime_notifyListNotifyOne (notifyListNotifyOne) returns if
// l.wait == l.notify (no waiter), and otherwise, under the list's lock,
// increments l.notify and readies the waiter holding the old value as its
// ticket, if it has parked yet (if not, its Wait sees the ticket notified and
// returns at once). The model is the same increment by compare-and-swap,
// retried if l.notify changed in between (as for NotifyAll).
func runtime_notifyListNotifyOne(l *notifyList) {
	for {
		n := atomic.LoadUint32(&l.notify)
		if n == atomic.LoadUint32(&l.wait) || atomic.CompareAndSwapUint32(&l.notify, n, n+1) {
			return
		}
	}
}

// MODEL: Go's runtime_notifyListCheck throws if size is not the runtime's
// size of notifyList; the type is the real one, so its size is the runtime's,
// and the check passes.
func runtime_notifyListCheck(size uintptr) {
}
