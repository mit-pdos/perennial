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

// A function that defers returns its results' values after the deferred calls
// have run: `return e` assigns the results first, and a deferred function
// literal may then read and modify the named results.

func deferAssignResult() (r uint64) {
	defer func() { r = 2 }()
	return 1
}

func deferIncrResult() (r uint64) {
	defer func() { r++ }()
	r = 1
	return
}

func deferRecoverResult() (r uint64) {
	defer func() {
		recover()
		r = 3
	}()
	return 1
}

// deferReadResult: the deferred function sees the result assigned by `return`.
func deferReadResult(g *uint64) (r uint64) {
	defer func() { *g = r }()
	return 5
}

// deferUnnamedResults: unnamed results are evaluated before the deferred calls.
func deferUnnamedResults() (uint64, bool) {
	x := uint64(1)
	defer func() { x = 2 }()
	return x, true
}

// deferShadowedResult: `return` assigns the result even where its name is
// shadowed.
func deferShadowedResult() (r uint64) {
	defer func() { r *= 2 }()
	if true {
		r := uint64(5)
		return r + 1
	}
	return 0
}

func deferPair() (uint64, uint64) {
	return 1, 2
}

// deferSwapResults: `return f()` with several results.
func deferSwapResults() (a, b uint64) {
	defer func() { a, b = b, a }()
	return deferPair()
}

func testDeferAssignResult() bool {
	return deferAssignResult() == 2
}

func testDeferIncrResult() bool {
	return deferIncrResult() == 2
}

func testDeferRecoverResult() bool {
	return deferRecoverResult() == 3
}

func testDeferReadResult() bool {
	g := uint64(0)
	r := deferReadResult(&g)
	return r == 5 && g == 5
}

func testDeferUnnamedResults() bool {
	x, ok := deferUnnamedResults()
	return x == 1 && ok
}

func testDeferShadowedResult() bool {
	return deferShadowedResult() == 12
}

func testDeferSwapResults() bool {
	a, b := deferSwapResults()
	return a == 2 && b == 1
}
