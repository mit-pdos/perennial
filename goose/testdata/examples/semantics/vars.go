package semantics

func testPointerAssignment() bool {
	var x bool
	x = true
	return x
}

func testAddressOfLocal() bool {
	var x = false
	xptr := &x
	*xptr = true
	return x && *xptr
}

func testAnonymousAssign() bool {
	_ = uint64(1) + uint64(2)
	return true
}
