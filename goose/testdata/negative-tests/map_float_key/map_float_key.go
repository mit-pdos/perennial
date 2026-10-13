package map_float_key

// Go's map compares keys with ==: a NaN key is never found again, -0 and +0
// are one key. The model compares keys by their bits.

func f(x float64) bool {
	m := map[float64]int{}
	m[x] = 1
	_, ok := m[x] // ERROR contains a float
	return ok
}
