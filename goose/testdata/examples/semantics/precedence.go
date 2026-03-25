package semantics

func testOrCompareSimple() bool {
	if 3 > 4 || 4 > 3 {
		return true
	}
	return false
}

func testOrCompare() bool {
	var ok = true
	if !(3 > 4 || 4 > 3) {
		ok = false
	}
	if 4 < 3 || 2 > 3 {
		ok = false
	} else {
	}
	return ok
}

func testAndCompare() bool {
	var ok = true
	if 3 > 4 && 4 > 3 {
		ok = false
	}
	if 4 > 3 || 2 < 3 {
	} else {
		ok = false
	}
	return ok
}

func testShiftMod() bool {
	return (20 >> (8 % 4)) == 20
}
