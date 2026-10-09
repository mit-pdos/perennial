package semantics

// each iteration of a loop has its own iteration variables

// the example of the Go spec: the copy for the next iteration is made before
// the post statement, from the current value
func testLoopVarClosures() bool {
	var prints []func() uint64
	for i := uint64(0); i < 5; i++ {
		prints = append(prints, func() uint64 { return i })
		i++
	}
	return len(prints) == 3 &&
		prints[0]() == 1 && prints[1]() == 3 && prints[2]() == 5
}

func testLoopVarAddress() bool {
	var ptrs []*uint64
	for i := uint64(0); i < 3; i++ {
		ptrs = append(ptrs, &i)
	}
	*ptrs[0] = 10
	return *ptrs[0] == 10 && *ptrs[1] == 1 && *ptrs[2] == 2
}

// the copy is also made after a continue
func testLoopVarContinue() bool {
	var ptrs []*uint64
	for i := uint64(0); i < 4; i++ {
		if i%2 == 0 {
			continue
		}
		ptrs = append(ptrs, &i)
	}
	return len(ptrs) == 2 && *ptrs[0] == 1 && *ptrs[1] == 3
}

// two variables, and no post statement
func testLoopVarsNoPost() bool {
	var fs []func() uint64
	for i, j := uint64(0), uint64(10); i < 2; {
		fs = append(fs, func() uint64 { return i + j })
		i++
		j++
	}
	return fs[0]() == 12 && fs[1]() == 14
}

func testRangeVarClosures() bool {
	var fs []func() uint64
	for i, x := range []uint64{10, 20} {
		fs = append(fs, func() uint64 { return uint64(i) + x })
	}
	return fs[0]() == 10 && fs[1]() == 21
}

func testRangeVarAddress() bool {
	var ptrs []*uint64
	for _, x := range []uint64{1, 2, 3} {
		ptrs = append(ptrs, &x)
	}
	return *ptrs[0] == 1 && *ptrs[1] == 2 && *ptrs[2] == 3
}

type loopCounter struct {
	n uint64
}

func (c *loopCounter) ptr() *loopCounter {
	return c
}

// calling a method with a pointer receiver takes the variable's address
func testRangeVarMethod() bool {
	var ps []*loopCounter
	for _, c := range []loopCounter{{n: 1}, {n: 2}} {
		ps = append(ps, c.ptr())
	}
	return ps[0].n == 1 && ps[1].n == 2
}

// a variable assigned by the loop (not declared by it) is shared
func testRangeVarShared() bool {
	var x uint64
	var ptrs []*uint64
	for _, x = range []uint64{1, 2} {
		ptrs = append(ptrs, &x)
	}
	return ptrs[0] == ptrs[1] && *ptrs[0] == 2
}

// with one variable shared by all iterations, f would return 3
func testLoopVarCapture() bool {
	var f func() uint64
	for i := uint64(0); i < 3; i++ {
		if i == 1 {
			f = func() uint64 { return i }
		}
	}
	return f() == 1
}
