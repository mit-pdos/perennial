package unittest

import (
	"sync"
)

// Skip is a placeholder for some impure code
func Skip() {}

func simpleSpawn() {
	l := new(sync.Mutex)
	v := new(uint64)
	go func() {
		l.Lock()
		x := *v
		if x > 0 {
			Skip()
		}
		l.Unlock()
	}()
	l.Lock()
	*v = 1
	l.Unlock()
}

func threadCode(tid uint64) {}

func loopSpawn() {
	for i := uint64(0); i < 10; i++ {
		i := i
		go func() {
			threadCode(i)
		}()
	}
	for dummy := true; ; {
		// do some work to avoid a self-assignment
		dummy = !dummy
		continue
	}
}
