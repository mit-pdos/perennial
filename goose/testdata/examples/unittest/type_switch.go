package unittest

func typeAssertInt(x any) int {
	return x.(int)
}

func wrapUnwrapInt() int {
	return typeAssertInt(1)
}

func checkedTypeAssert(x any) uint64 {
	if v, ok := x.(uint64); ok {
		return v
	}
	return 3
}

func basicTypeSwitch(x any) int {
	switch x.(type) {
	case int:
		return 1
	case string:
		return 2
	}
	return 0
}

func fancyTypeSwitch(x any) int {
	var r int
	switch z := 0; y := x.(type) {
	case int:
		return y
	default:
		z = 3
		r = z
	case string:
		return 2
	case nil:
		return 4
	}
	return r
}

func multiTypeSwitch(x any) int {
	switch x.(type) {
	case int, string:
		return 1
	}
	return 0
}
