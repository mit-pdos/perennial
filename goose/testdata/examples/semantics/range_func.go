package semantics

import "iter"

// helpers
func countTo(n uint64) func(yield func(uint64) bool) {
	return func(yield func(uint64) bool) {
		for i := uint64(0); i < n; i++ {
			if !yield(i) {
				return
			}
		}
	}
}

func pairsTo(n uint64) func(yield func(uint64, uint64) bool) {
	return func(yield func(uint64, uint64) bool) {
		for i := uint64(0); i < n; i++ {
			if !yield(i, 10*i) {
				return
			}
		}
	}
}

func times(n uint64) func(yield func() bool) {
	return func(yield func() bool) {
		for range n {
			if !yield() {
				return
			}
		}
	}
}

func seqOf(xs []uint64) iter.Seq2[uint64, uint64] {
	return func(yield func(uint64, uint64) bool) {
		for i, x := range xs {
			if !yield(uint64(i), x) {
				return
			}
		}
	}
}

func findRangeFunc(n, x uint64) (uint64, bool) {
	for i := range countTo(n) {
		if i == x {
			return i, true
		}
	}
	return 0, false
}

func findNestedRangeFunc(n, x uint64) uint64 {
	for i := range countTo(n) {
		for j := range countTo(n) {
			if i*j == x {
				return 10*i + j
			}
		}
	}
	return 0
}

// The named result r is assigned by the return in the body, then overwritten
// by the range function after the loop body ends; Go returns the final value.
func namedResultRangeFunc(explicit bool) (r uint64) {
	f := func(yield func() bool) {
		yield()
		r = 7
	}
	for range f {
		if explicit {
			return 5
		}
		return
	}
	return 3
}

// The return assigns the named result r, not the r declared in the body.
func shadowedResultRangeFunc() (r uint64) {
	for range times(1) {
		r := uint64(3)
		return r + 1
	}
	return 0
}

func blankResultRangeFunc() (_ uint64) {
	for range times(1) {
		return 3
	}
	return 0
}

func panicAfterYield(yield func() bool) {
	yield()
	panic("after")
}

// The return in the body sets the (unnamed) result, which the function returns
// when it recovers from the range function's panic after the body ended.
func unnamedResultRangeFuncRecover() uint64 {
	defer func() { recover() }()
	for range panicAfterYield {
		return 1
	}
	return 2
}

func twoResults(a, b uint64) (uint64, uint64) {
	return a, b
}

func unnamedResultsRangeFunc() (uint64, uint64) {
	for i := range countTo(5) {
		if i == 3 {
			return twoResults(i, 10*i)
		}
	}
	return 0, 0
}

// tests
func testRangeFuncSum() bool {
	var sum uint64
	for i := range countTo(5) {
		sum += i
	}
	return sum == 10
}

func testRangeFuncPairs() bool {
	var sum uint64
	for i, v := range pairsTo(4) {
		sum += i + v
	}
	var keys uint64
	for i := range pairsTo(4) {
		keys += i
	}
	return sum == 66 && keys == 6
}

func testRangeFuncNoValues() bool {
	var n uint64
	for range times(3) {
		n++
	}
	for range countTo(2) {
		n++
	}
	return n == 5
}

func testRangeFuncBreakContinue() bool {
	var sum uint64
	for i := range countTo(100) {
		if i%2 == 0 {
			continue
		}
		if i > 7 {
			break
		}
		sum += i
	}
	return sum == 1+3+5+7
}

func testRangeFuncBreakInSwitch() bool {
	var sum uint64
	for i := range countTo(5) {
		switch i {
		case 2:
			break
		default:
			sum += i
		}
	}
	return sum == 8
}

func testRangeFuncReturn() bool {
	i, ok := findRangeFunc(10, 4)
	_, ok2 := findRangeFunc(3, 4)
	return i == 4 && ok && !ok2
}

func testRangeFuncNestedReturn() bool {
	return findNestedRangeFunc(5, 6) == 23
}

func testRangeFuncNamedResult() bool {
	return namedResultRangeFunc(true) == 7 && namedResultRangeFunc(false) == 7
}

func testRangeFuncAssign() bool {
	var i, v uint64
	for i, v = range pairsTo(3) {
	}
	return i == 2 && v == 20
}

func testRangeFuncLoopVars() bool {
	var fs []func() uint64
	for i := range countTo(3) {
		fs = append(fs, func() uint64 { return i })
	}
	return fs[0]() == 0 && fs[1]() == 1 && fs[2]() == 2
}

func testRangeFuncDefer() bool {
	var log []uint64
	func() {
		for i := range countTo(3) {
			defer func() { log = append(log, i) }()
		}
		log = append(log, 9)
	}()
	return len(log) == 4 && log[0] == 9 && log[1] == 2 && log[2] == 1 && log[3] == 0
}

func testRangeFuncPanic() (ok bool) {
	var after bool
	defer func() {
		ok = recover() != nil && !after
	}()
	f := func(yield func() bool) {
		yield()
		after = true
	}
	for range f {
		panic("body")
	}
	return false
}

func testRangeFuncIterSeq() bool {
	var sum uint64
	for i, x := range seqOf([]uint64{3, 4, 5}) {
		sum += i * x
	}
	var seq iter.Seq[uint64] = countTo(4)
	for i := range seq {
		sum += i
	}
	return sum == 14+6
}

func testRangeFuncShadowedBlankResults() bool {
	return shadowedResultRangeFunc() == 4 && blankResultRangeFunc() == 3
}

func testRangeFuncUnnamedResultRecover() bool {
	return unnamedResultRangeFuncRecover() == 1
}

func testRangeFuncUnnamedResults() bool {
	a, b := unnamedResultsRangeFunc()
	return a == 3 && b == 30
}
