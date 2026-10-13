package evalorder_assign

// Go calls g before h (left to right); goose's translation of a single
// assignment evaluates the right side first.

func g() uint64 { return 0 }
func h() uint64 { return 1 }

func f(a []uint64) {
	a[g()] = h() // ERROR evaluation order
}
