package unittest

import "sync"

func condvarWrapping() {
	var mu *sync.Mutex
	mu = new(sync.Mutex)
	cond1 := sync.NewCond(mu)
	mu = new(sync.Mutex)
	cond1.Wait()
}
