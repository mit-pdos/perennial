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

func deferVariadicCount(n *uint64, xs ...uint64) {
	*n = 100 + uint64(len(xs))
	for _, x := range xs {
		*n += x
	}
}

func deferVariadicPair(n *uint64) (*uint64, uint64) {
	return n, 7
}

func testDeferVariadic() bool {
	n0, n2, n1 := new(uint64), new(uint64), new(uint64)
	func() {
		defer deferVariadicCount(n0)
		defer deferVariadicCount(n2, 3, 4)
		defer deferVariadicCount(deferVariadicPair(n1))
	}()
	return *n0 == 100 && *n2 == 109 && *n1 == 108
}
