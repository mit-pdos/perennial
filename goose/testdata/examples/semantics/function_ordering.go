package semantics

// helpers
type Editor struct {
	s        []uint64
	next_val uint64
}

// advances the array editor, and returns the value it wrote, storing
// "next" in next_val
func (e *Editor) AdvanceReturn(next uint64) uint64 {
	var tmp = e.next_val
	e.s[0] = tmp
	e.next_val = next
	e.s = e.s[1:]
	return tmp
}

// we call this function with side-effectful function calls as arguments,
// its implementation is unimportant
func addFour64(a uint64, b uint64, c uint64, d uint64) uint64 {
	return a + b + c + d
}

type Pair struct {
	x uint64
	y uint64
}

// tests
func failing_testFunctionOrdering() bool {
	var arr = make([]uint64, 5)

	e1 := Editor{s: arr[0:], next_val: 1}
	e2 := Editor{s: arr[0:], next_val: 101}

	if e1.AdvanceReturn(2)+e2.AdvanceReturn(102) != 102 {
		return false
	}
	// e2.AdvanceReturn should be called second.
	if arr[0] != 101 {
		return false
	}

	if addFour64(e1.AdvanceReturn(3),
		e2.AdvanceReturn(103),
		e2.AdvanceReturn(104),
		e1.AdvanceReturn(4)) != 210 {
		return false
	}

	if arr[1] != 102 {
		return false
	}

	if arr[2] != 3 {
		return false
	}

	// function calls in struct initializer
	p := Pair{x: e1.AdvanceReturn(5), y: e2.AdvanceReturn(105)}
	if arr[3] != 104 {
		return false
	}

	// y initializer executes first if listed first
	q := Pair{y: e1.AdvanceReturn(6), x: e2.AdvanceReturn(106)}
	if arr[4] != 105 {
		return false
	}
	return p.x+q.x == 109
}

func storeAndReturn(x *uint64, v uint64) uint64 {
	*x = v
	return v
}

// Goose has a right-to-left evaluation order for function arguments,
// which is incorrect.
func failing_testArgumentOrder() bool {
	var x = uint64(0)
	addFour64(storeAndReturn(&x, 1), storeAndReturn(&x, 2),
		storeAndReturn(&x, 3), storeAndReturn(&x, 4))
	ok := x == 4
	return ok
}
