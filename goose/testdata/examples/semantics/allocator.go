package semantics

// patterns that show up in in-memory allocators

type unit struct{}

func findKey(m map[uint64]unit) (uint64, bool) {
	var found uint64 = 0
	var ok bool = false
	for k := range m {
		if !ok {
			found = k
			ok = true
		}
		// TODO: goose doesn't support break in map iteration
	}
	return found, ok
}

func allocate(m map[uint64]unit) (uint64, bool) {
	k, ok := findKey(m)
	delete(m, k)
	return k, ok
}

func freeRange(sz uint64) map[uint64]unit {
	m := make(map[uint64]unit)
	for i := uint64(0); i < sz; i++ {
		m[i] = unit{}
	}
	return m
}

func testAllocateDistinct() bool {
	free := freeRange(4)
	a1, _ := allocate(free)
	a2, _ := allocate(free)
	return a1 != a2
}

func testAllocateFull() bool {
	free := freeRange(2)
	_, ok1 := allocate(free)
	_, ok2 := allocate(free)
	_, ok3 := allocate(free)
	return ok1 && ok2 && !ok3
}
