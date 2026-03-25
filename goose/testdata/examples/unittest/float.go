package unittest

const (
	a = 1.0
	b = 1e6
)

func useFloat() float64 {
	x := a
	x = (x + a) * 1.0
	return x
}

func compareIntFloat(x int) bool {
	return x < b
}

func compareFloatInt(x int) bool {
	return b < x
}
