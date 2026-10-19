package inits

var x uint64
var y uint64

func init() {
	x = 1
}

func init() {
	y = 2
}

// z's initializer is trusted: z'init is defined in TrustedCode.
var z = computeZ()

func computeZ() uint64 {
	return 3
}
