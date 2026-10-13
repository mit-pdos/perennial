package float_range_iface

func f(xs []float64) any {
	var a any
	for _, a = range xs { // ERROR contains a float, to an interface
	}
	return a
}
