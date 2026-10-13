package float_into_iface

// an interface holding a float could be a map key, which the model compares by bits
func box(x float64) any {
	return x // ERROR contains a float, to an interface
}
