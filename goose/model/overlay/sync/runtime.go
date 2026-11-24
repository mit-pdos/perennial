// The Go model of sync's runtime hooks (Perennial/Code/sync.toml, [model]),
// spliced into runtime.go in place of the real declarations. Each real one is
// a function with no Go body that the runtime defines by a push linkname
// (runtime/sema.go); the overlay blanks those directives, so that gc links
// these bodies instead.

package sync

import (
	"internal/gomodel"
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
// only orders the waiters).
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

// MODEL: Go's runtime_notifyListAdd (runtime/sema.go, notifyListAdd) returns
// the next ticket of the runtime's counter l.wait and increments it; the
// ticket is used only by runtime_notifyListWait. The model's Wait does not
// use it and the model keeps no counter, so the ticket is an arbitrary
// uint32 (gomodel.ChooseUint64), which covers the runtime's, and l is not
// written.
func runtime_notifyListAdd(l *notifyList) uint32 {
	return uint32(gomodel.ChooseUint64())
}

// MODEL: Go's runtime_notifyListWait parks until ticket t is notified. The
// model returns at once: Cond.Wait's callers must anyway allow for Wait
// returning when the condition does not hold, and the return happens in
// every schedule where Go's does, so the model has all of Go's behaviours
// (and more).
func runtime_notifyListWait(l *notifyList, t uint32) {
}

// MODEL: Go's wakes every goroutine parked in runtime_notifyListWait; the
// model's Wait never parks, so there is nothing to wake.
func runtime_notifyListNotifyAll(l *notifyList) {
}

// MODEL: as runtime_notifyListNotifyAll, for one goroutine.
func runtime_notifyListNotifyOne(l *notifyList) {
}

// MODEL: Go's runtime_notifyListCheck throws if size is not the runtime's
// size of notifyList; the type is the real one, so its size is the runtime's,
// and the check passes.
func runtime_notifyListCheck(size uintptr) {
}
