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

func panicInLoop() {
	for i := uint64(0); ; i++ {
		if i == 3 {
			panic("loop")
		}
	}
}

func panicTwoDeep() {
	panicInLoop()
}

// catchTwoDeep recovers a panic raised two calls down, inside a loop.
func catchTwoDeep() (ok bool) {
	defer func() {
		if recover() != nil {
			ok = true
		}
	}()
	panicTwoDeep()
	return false
}

// panicUnrecovered runs its deferred function and keeps panicking.
func panicUnrecovered() {
	defer func() {}()
	panic("unrecovered")
}

func testRecoverNamed() bool {
	return recoverNamed() == 42
}

func testCatchTwoDeep() bool {
	return catchTwoDeep()
}
