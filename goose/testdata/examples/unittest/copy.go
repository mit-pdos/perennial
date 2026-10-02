package unittest

func testCopySimple() bool {
	x := make([]byte, 10)
	x[3] = 1
	y := make([]byte, 10)
	copy(y, x)
	return y[3] == 1
}

func testCopyDifferentLengths() bool {
	x := make([]byte, 15)
	x[3] = 1
	x[12] = 2
	y := make([]byte, 10)
	n := uint64(copy(y, x))
	return n == 10 && y[3] == 1
}
