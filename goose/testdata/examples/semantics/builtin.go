package semantics

func testMinUint64() bool {
	x := uint64(10)
	return min(x, 1) == 1
}

func testMaxUint64() bool {
	x := uint64(10)
	return max(x, 1) == 10
}
