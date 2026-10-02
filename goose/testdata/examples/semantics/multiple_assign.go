package semantics

func multReturnTwo() (uint64, uint64) {
	return 2, 3
}

func testAssignTwo() bool {
	var x uint64 = 10
	var y uint64 = 15
	x, y = multReturnTwo()
	return x == 2 && y == 3
}

func multReturnThree() (uint64, bool, uint32) {
	return 2, true, 1
}

func testAssignThree() bool {
	var x uint64 = 10
	var y bool = false
	var z uint32 = 15
	x, y, z = multReturnThree()
	return x == 2 && y == true && z == 1
}

func testMultipleAssignToMap() bool {
	var x uint64 = 10
	var m = make(map[uint64]uint64)
	x, m[0] = multReturnTwo()
	return x == 2 && m[0] == 3
}
