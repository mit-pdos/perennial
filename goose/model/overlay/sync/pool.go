// The Go model of sync.Pool's Get and Put (Perennial/Code/sync.toml,
// [model]), spliced into pool.go in place of the real declarations, with its
// helpers added. The type Pool is the real one, translated; the model keeps
// its state in Pool's field local (an unsafe.Pointer, where Go keeps its
// per-P pools).

package sync

import (
	"internal/gomodel"
	"sync/atomic"
	"unsafe"
)

// poolModel is the model's state of a Pool: a multiset of the values Put and
// not yet taken by a Get, under a lock. It is more nondeterministic than gc's
// per-P pools, their victim cache and the clearing of both at each GC, so that
// it covers them: Put may drop its value, and Get may ignore the pool even
// when it is not empty; otherwise Get removes and returns an arbitrary
// element. Each value Put is returned by at most one Get, as in gc, and the
// lock makes a Put of x synchronize before the Get returning x, as the Pool
// documentation promises.
type poolModel struct {
	mu    Mutex
	items []any
}

// poolModelOf returns the state of the pool p, installing a new, empty one on
// first use: p.local is nil in a zero Pool, and only this function writes it,
// with a compare-and-swap from nil, so that racing first calls of Get and Put
// agree on one state.
func poolModelOf(p *Pool) *poolModel {
	for {
		if l := atomic.LoadPointer(&p.local); l != nil {
			return poolModelAt(l)
		}
		atomic.CompareAndSwapPointer(&p.local, nil, unsafe.Pointer(new(poolModel)))
	}
}

// poolModelAt is (*poolModel)(l): a primitive stub (GooseLang: the identity on
// the address, Perennial/TrustedCode/sync.lean), since the semantics converts
// an unsafe.Pointer only to a pointer to a plain type. poolModelOf calls it
// only on a non-nil value of a Pool's field local, which is unexported and
// which, with Get and Put modelled, only poolModelOf writes, always with a
// *poolModel: so l is a *poolModel converted to unsafe.Pointer, and the
// conversion back is the identity, in Go as in the model.
func poolModelAt(l unsafe.Pointer) *poolModel {
	return (*poolModel)(l)
}

// MODEL: Go's Put ignores nil and otherwise pins the goroutine to its P and
// stores x in that P's private slot or pushes it onto the P's lock-free
// shared chain; the GC later moves the per-P pools to the victim cache and
// then drops them. Goose translates it, but the translation is stuck at
// indexLocal's conversion of a uintptr back to an unsafe.Pointer (pointer
// arithmetic) and at poolDequeue's store of an any through an
// unsafe.Pointer to its eface; runtime_procPin, which keeps the goroutine on
// its P, has no Go body. The model ignores nil as Go does, and otherwise
// adds x to the pool's state or drops it (gomodel.Choose: the GC may drop it
// in Go before any Get).
func (p *Pool) Put(x any) {
	if x == nil {
		return
	}
	s := poolModelOf(p)
	if gomodel.Choose() {
		return
	}
	s.mu.Lock()
	s.items = append(s.items, x)
	s.mu.Unlock()
}

// MODEL: Go's Get pins the goroutine to its P and takes the P's private
// value, else pops its shared chain, else steals from other Ps and the
// victim cache (getSlow); if it found nothing and New is not nil, it returns
// New(). Goose translates it but is stuck as for Put. The model's search
// takes an arbitrary element of the pool's state or nothing, even when the
// state is not empty (gomodel.Choose: Go's search may miss values in other
// Ps' chains or dropped by the GC, and gomodel.ChooseUint64: which value it
// finds); the rest, calling New, is Go's.
func (p *Pool) Get() any {
	s := poolModelOf(p)
	var x any
	s.mu.Lock()
	n := uint64(len(s.items))
	if n != 0 && !gomodel.Choose() {
		i := gomodel.ChooseUint64() % n
		x = s.items[i]
		s.items[i] = s.items[n-1]
		s.items = s.items[:n-1]
	}
	s.mu.Unlock()
	if x == nil && p.New != nil {
		x = p.New()
	}
	return x
}

// MODEL: Go's runtime_registerPoolCleanup (a runtime push linkname, no Go
// body) records poolCleanup for the GC to call at the start of each cycle;
// poolCleanup moves the per-P pools to the victim cache. The model has no GC,
// and its pools' state is not in the per-P pools, which only the replaced
// Get and Put used, so recording it changes nothing.
func runtime_registerPoolCleanup(cleanup func()) {
}
