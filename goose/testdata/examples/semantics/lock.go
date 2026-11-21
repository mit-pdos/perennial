package semantics

import "sync"

// We can't interpret multithreaded code, so this just checks that
// locks are correctly interpreted
func testsUseLocks() bool {
	m := new(sync.Mutex)
	m.Lock()
	m.Unlock()
	return true
}

type mutexHolder struct {
	mu sync.Mutex
	x  uint64
}

// A mutex from a composite literal is unlocked, alone or as a field of a
// struct literal.
func testMutexLiteral() bool {
	m := sync.Mutex{}
	h := mutexHolder{mu: sync.Mutex{}, x: 1}
	return m.TryLock() && h.mu.TryLock()
}
