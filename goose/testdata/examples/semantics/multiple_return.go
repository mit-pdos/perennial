package semantics

func returnTwo() (uint64, uint64) {
	return 2, 3
}

func testReturnTwo() bool {
	x, y := returnTwo()
	return x == 2 && y == 3
}

func testAnonymousBinding() bool {
	_, y := returnTwo()
	return y == 3
}

func returnThree() (uint64, bool, uint32) {
	return 2, true, 1
}

func testReturnThree() bool {
	x, y, z := returnThree()
	return x == 2 && y == true && z == 1
}

func returnFour() (uint64, bool, uint32, uint64) {
	return 2, true, 1, 7
}

func testReturnFour() bool {
	x, y, z, w := returnFour()
	return x == 2 && y == true && z == 1 && w == 7
}
