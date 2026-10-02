package semantics

func testCompareAll() bool {
	var ok = true
	var nok = false

	ok = ok && (1 < 2)
	nok = ok && (2 < 1)

	ok = ok && (1 <= 2)
	ok = ok && (2 <= 2)
	nok = ok && (2 <= 1)

	if nok {
		return false
	}
	return ok
}

func testCompareGT() bool {
	var x uint64 = 4
	var y uint64 = 5

	var ok = true
	ok = ok && (y > 4)
	ok = ok && (y > x)

	return ok
}

func testCompareGE() bool {
	var x uint64 = 4
	var y uint64 = 5

	var ok = true
	ok = ok && (y >= 4)
	ok = ok && (y >= 5)
	ok = ok && (y >= x)

	if y > 5 {
		return false
	}

	return ok
}

func testCompareLT() bool {
	var x uint64 = 4
	var y uint64 = 5

	var ok = true
	ok = ok && (y < 6)
	ok = ok && (x < y)

	return ok
}

func testCompareLE() bool {
	var x uint64 = 4
	var y uint64 = 5

	var ok = true
	ok = ok && (y <= 6)
	ok = ok && (y <= 5)
	ok = ok && (x <= y)

	if y < 5 {
		return false
	}

	return ok
}
