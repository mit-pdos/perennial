package float_type_arg

// A float type argument could become a map key inside the generic code.

func Count[K comparable](ks []K) int {
	m := map[K]bool{}
	for _, k := range ks {
		m[k] = true
	}
	return len(m)
}

func f(xs []float64) int {
	return Count[float64](xs) // ERROR contains a float
}
