package unittest

func testSwitchVal(x uint64) bool {
	switch x {
	default:
		return false
	case 0:
		return true
	case 1:
		return false
	}
}

func testSwitchMultiple(x uint64) int {
	switch x {
	case 10, 1:
		return 1
	case 0:
		return 2
	}
	return 3
}
