package unittest

type composite struct {
	a uint64
	b uint64
}

func ReassignVars() {
	var x uint64
	y := uint64(0)
	x = 3
	var z = composite{a: x, b: y}
	z = composite{a: y, b: x}
	x = z.a
}
