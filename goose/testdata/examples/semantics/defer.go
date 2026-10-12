package semantics

func deferSimple() *uint64 {
	x := new(uint64)
	for i := uint64(0); i < 10; i++ {
		defer func() {
			*x += 1
		}()
	}
	return x
}

func testDefer() bool {
	return *(deferSimple()) == 10
}

func testDeferFuncLit() bool {
	x := 10
	f := func() {
		defer func() {
			x += 1
		}()
	}
	f()
	return x == 11
}

// a deferred call sees (and may change) the value a `return` gives a named result
func namedResultDefer() (x uint64) {
	defer func() {
		x += 1
	}()
	return 10
}

func testNamedResultDefer() bool {
	return namedResultDefer() == 11
}

// the named result gets the returned value even in the scope of a variable hiding it
func namedResultShadowed() (x uint64) {
	defer func() {
		if x == 5 {
			x = 7
		}
	}()
	if x := uint64(5); x > 0 {
		return x
	}
	return 0
}

func testNamedResultShadowed() bool {
	return namedResultShadowed() == 7
}
