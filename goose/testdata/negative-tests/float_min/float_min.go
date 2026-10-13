package float_min

func f(x, y float64) float64 {
	return min(x, y) // ERROR min of floats
}
