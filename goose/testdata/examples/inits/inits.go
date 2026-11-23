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

// w has no initializer and is trusted (as runtime.buildVersion, which the
// linker sets): initialize' runs w'init, defined in TrustedCode, in place of
// allocating it.
var w uint64

func computeZ() uint64 {
	return 3
}

// c and d have one initializer and are axiomatized: initialize' runs c.init
// and then d.init (perennial#657: goose ran c.init only).
var c, d = pair()

func pair() (uint64, uint64) { return 1, 2 }
