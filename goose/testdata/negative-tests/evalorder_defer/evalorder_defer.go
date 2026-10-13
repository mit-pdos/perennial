package evalorder_defer

// Go evaluates a deferred call's function value (h(1)) before its arguments
// (g(2)); goose's translation evaluates the arguments first.

func g(k uint64) uint64          { return k }
func h(k uint64) func(uint64)    { return func(uint64) {} }

func f() {
	defer h(1)(g(2)) // ERROR evaluation order
}
