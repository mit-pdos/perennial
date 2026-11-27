package semantics

// A value sent in a select send case, or assigned by a range clause, is
// converted to the channel's element type or the iteration variable's type.

type assignabilityT struct{ x uint64 }

func testSelectSendInterface() bool {
	ch := make(chan interface{}, 1)
	p := &assignabilityT{x: 1}
	select {
	case ch <- p:
	}
	q, ok := (<-ch).(*assignabilityT)
	return ok && q == p
}

func testRangeAssignInterface() bool {
	var x interface{}
	for _, x = range []*assignabilityT{{x: 2}} {
	}
	q, ok := x.(*assignabilityT)
	return ok && q.x == 2
}
