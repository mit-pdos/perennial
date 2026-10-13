package map_float_struct_key

type P struct {
	X, Y float64
}

func f(p P) int {
	m := make(map[P]int)
	m[p] = 1
	return len(m) // ERROR contains a float
}
