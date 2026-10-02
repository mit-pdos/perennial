package semantics

func testCopySimple() bool {
	x := make([]byte, 10)
	x[3] = 1
	y := make([]byte, 10)
	copy(y, x)
	return y[3] == 1
}

func testCopyShorterDst() bool {
	x := make([]byte, 15)
	x[3] = 1
	x[12] = 2
	y := make([]byte, 10)
	n := uint64(copy(y, x))
	return n == 10 && y[3] == 1
}

func testCopyShorterSrc() bool {
	x := make([]byte, 10)
	y := make([]byte, 15)
	x[3] = 1
	y[12] = 2
	n := uint64(copy(y, x))
	return n == 10 && y[3] == 1 && y[12] == 2
}
