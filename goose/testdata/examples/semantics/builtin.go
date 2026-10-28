package semantics

func testMinUint64() bool {
	x := uint64(10)
	return min(x, 1) == 1
}

func testMaxUint64() bool {
	x := uint64(10)
	return max(x, 1) == 10
}

type minMaxDur int64

func testMinMaxNamed() bool {
	d := minMaxDur(10)
	e := minMaxDur(-3)
	return min(d, e) == -3 && max(d, e) == 10 && max(e, 3) == 3
}

func minGeneric[T ~int64 | ~uint64](a, b T) T {
	return min(a, b)
}

func testMinGeneric() bool {
	return minGeneric(uint64(4), uint64(7)) == 4 && minGeneric(minMaxDur(5), minMaxDur(-2)) == -2
}
