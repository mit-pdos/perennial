package semantics

func IterateMapKeys(m map[uint64]uint64) uint64 {
	var sum uint64
	for k := range m {
		sum = sum + k
	}
	return sum
}

func IterateMapValues(m map[uint64]uint64) uint64 {
	var sum uint64
	for _, v := range m {
		sum = sum + v
	}
	return sum
}

func testIterateMap() bool {
	var ok = true

	// make a map with some things in it
	m := make(map[uint64]uint64)
	m[0] = 1
	m[1] = 2
	m[3] = 4

	// iterate keys
	ok = ok && (IterateMapKeys(m) == 4)

	// iterate values
	ok = ok && (IterateMapValues(m) == 7)

	return ok
}

func testMapSize() bool {
	var ok = true

	m := make(map[uint64]uint64)
	ok = ok && (uint64(len(m)) == 0)

	m[0] = 1
	m[1] = 2
	m[3] = 4
	ok = ok && (uint64(len(m)) == 3)

	return ok
}
