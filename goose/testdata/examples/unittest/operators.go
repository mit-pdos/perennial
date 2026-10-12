package unittest

func LogicalOperators(b1 bool, b2 bool) bool {
	return b1 && (b2 || b1) && !false
}

func LogicalAndEqualityOperators(b1 bool, x uint64) bool {
	return x == 3 && b1 == true
}

func ArithmeticShifts(x uint32, y uint64) uint64 {
	return uint64(x<<3) + (y << uint64(x)) + (y << 1)
}

// The count of a shift keeps its own type, not converted to the type of the
// shifted operand: uint8(1) << uint64(256) is 0.
func ShiftWideCount(x uint8, s uint64) uint8 {
	return x << s
}

// A signed count panics if it is negative.
func ShiftSignedCount(x uint32, s int) uint32 {
	return x >> s
}

func SignedShiftRight(x int8, s uint8) int8 {
	return x >> s
}

// The count may have a type-parameter type: whether it is signed depends on the
// instantiation.
func ShiftTypeParamCount[T ~int8 | ~uint](x int, y T) int {
	return x << y
}

func Complement(x uint64, y int32) uint64 {
	return ^x + uint64(^y)
}

func BitwiseOps(x uint32, y uint64) uint64 {
	return uint64(x) | uint64(uint32(y))&43
}

func Comparison(x uint64, y uint64) bool {
	if x < y {
		return true
	}
	if x == y {
		return true
	}
	if x != y {
		return true
	}
	if x > y {
		return true
	}
	if x+1 > y-2 {
		return true
	}
	return false
}

func AssignOps() {
	var x uint64
	x += 3
	x -= 3
	x++
	x--
}

func BitwiseAndNot(x uint32, y uint64) uint64 {
	z := uint64(x) &^ y
	z &^= 0xff
	return z
}

func Negative() {
	var x int64 = -10
	x += 3
}
