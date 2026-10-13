package float_select_iface

func f(ch chan any, x float64) {
	select {
	case ch <- x: // ERROR contains a float, to an interface
	}
}
