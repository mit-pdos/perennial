package unittest

import "sync"

func useLocks() {
	m := new(sync.Mutex)
	m.Lock()
	m.Unlock()
}

func useCondVar() {
	m := new(sync.Mutex)
	c := sync.NewCond(m)
	m.Lock()
	c.Signal()
	// NOTE: this example is artificial and deadlocks here
	c.Wait()
	m.Unlock()
}

type hasCondVar struct {
	// sync.Cond on its own is not supported
	cond *sync.Cond
}
