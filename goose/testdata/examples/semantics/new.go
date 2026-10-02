package semantics

func testNilDefault() bool {
	x := new(int)
	*x = 1
	return true
}

func testNilVal() bool {
	x := new(3)
	return *x == 3
}
