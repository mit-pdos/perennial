package float_elided_ptr_iface

type box struct{ I any }

// an elided &box{...} element builds a box, converting the float into I
func f(x float64) []*box {
	return []*box{{x}} // ERROR contains a float, to an interface
}
