package semantics

// recoverNamed panics; the deferred function recovers and sets the named result.
func recoverNamed() (x uint64) {
	defer func() {
		if r := recover(); r != nil {
			x = 42
		}
	}()
	panic("boom")
}

// recoverInLoop panics in the fourth iteration of its loop. The panic ends the
// loop (as a return would); the deferred function recovers it and sets the
// named result.
func recoverInLoop() (n uint64) {
	defer func() {
		if recover() != nil {
			n = 7
		}
	}()
	for i := uint64(0); ; i++ {
		if i == 3 {
			panic("loop")
		}
	}
}

func testRecoverNamed() bool {
	return recoverNamed() == 42
}

func testRecoverInLoop() bool {
	return recoverInLoop() == 7
}
