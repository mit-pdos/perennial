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
