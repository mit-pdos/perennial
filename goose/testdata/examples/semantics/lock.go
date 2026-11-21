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
// struct literal: Lock returns, and Unlock (a fatal error on an unlocked
// mutex) does not fail.
func testMutexLiteral() bool {
	m := sync.Mutex{}
	m.Lock()
	m.Unlock()
	h := mutexHolder{mu: sync.Mutex{}, x: 1}
	h.mu.Lock()
	h.mu.Unlock()
	return true
}
