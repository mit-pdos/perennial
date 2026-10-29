// Package pool is the Go model of the state of a sync.Pool, used by the
// trusted sync.(*Pool).Get and sync.(*Pool).Put (Perennial/TrustedCode/sync.lean),
// which keep a *Pool in the sync.Pool's field local.
//
// A Pool is a multiset of the values Put and not yet taken by a Get. It is
// more nondeterministic than gc's per-P pools, its victim cache and their
// clearing at each GC, so that it covers them: Put may drop its value, and Get
// may ignore the pool, even when it is not empty; otherwise Get removes and
// returns an arbitrary element. Each value Put is returned by at most one Get,
// as in gc, and the lock makes a Put of x synchronize before the Get returning
// x, as the sync.Pool documentation promises.
package pool

import (
	"github.com/goose-lang/primitive"
)

// Pool is the state of a sync.Pool. Its zero value is an empty pool.
type Pool struct {
	mu    primitive.Mutex
	items []any
}

// Put adds x to the pool, or drops it. x is not nil (sync.(*Pool).Put ignores
// nil).
func (p *Pool) Put(x any) {
	if primitive.RandomUint64() == 0 {
		return
	}
	p.mu.Lock()
	p.items = append(p.items, x)
	p.mu.Unlock()
}

// Get removes an arbitrary element of the pool and returns it, or returns nil
// (even when the pool is not empty).
func (p *Pool) Get() any {
	p.mu.Lock()
	n := uint64(len(p.items))
	if n == 0 || primitive.RandomUint64() == 0 {
		p.mu.Unlock()
		return nil
	}
	i := primitive.RandomUint64() % n
	x := p.items[i]
	p.items[i] = p.items[n-1]
	p.items = p.items[:n-1]
	p.mu.Unlock()
	return x
}
