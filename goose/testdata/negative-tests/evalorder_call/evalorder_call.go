package evalorder_call

// Go evaluates the receiver's operands (g) before the arguments (h); goose's
// translation evaluates the arguments first.

type S struct{}

func (S) M(x uint64) {}

func g() uint64 { return 0 }
func h() uint64 { return 1 }

func f(ps []S) {
	ps[g()].M(h()) // ERROR evaluation order
}
