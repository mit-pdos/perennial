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
