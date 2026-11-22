package semantics

// labeled break and continue: `break L` and `continue L` aimed at a labeled
// for, range, switch or select statement

// labeledContinue: `continue L` from an inner for to an outer labeled for that
// has a post statement (i++), which must run. Iteration i adds 0+1+...+i, then
// the inner loop jumps to the next outer iteration when j > i.
// Returns 0 + 1 + 3 + 6 = 10.
func labeledContinue() uint64 {
	var sum uint64
L:
	for i := uint64(0); i < 4; i++ {
		for j := uint64(0); j < 4; j++ {
			if j > i {
				continue L
			}
			sum += j
		}
	}
	return sum
}

// labeledBreak: `break L` from an inner for ends the outer labeled for.
// Counts the pairs (i, j) with i*10+j < 23. Returns 23.
func labeledBreak() uint64 {
	var n uint64
L:
	for i := uint64(0); i < 10; i++ {
		for j := uint64(0); j < 10; j++ {
			if i*10+j == 23 {
				break L
			}
			n++
		}
	}
	return n
}

// breakLoopFromSwitch: `break L` in a switch inside a labeled for ends the for;
// the unlabeled break only ends the switch. Returns 1 + 0 + 1 = 2 (i = 0, 1, 2;
// i = 1 breaks the switch only; i = 3 ends the loop).
func breakLoopFromSwitch() uint64 {
	var n uint64
L:
	for i := uint64(0); i < 10; i++ {
		switch i {
		case 1:
			break
		case 3:
			break L
		default:
			n++
		}
	}
	return n
}

// continueFromNestedSwitch: the shape in Go's doPrintf (print.go), `continue L`
// inside switch, inside switch, inside an inner for with a post statement,
// aimed at an outer for without one. The inner post statement must not run.
// Returns 3 (i = 0, 2, 4; odd i are skipped by continue L).
func continueFromNestedSwitch() uint64 {
	var n uint64
	var i uint64 = 0
L:
	for i < 6 {
		for j := uint64(0); j < 2; j++ {
			switch j {
			case 0:
				switch i % 2 {
				case 1:
					i++
					continue L
				}
			default:
				n++
			}
		}
		i++
	}
	return n
}

// labeledSwitch: `break L` of a labeled switch, from a for inside a case.
// An unlabeled break there would only end the for. Returns 2 (the loop runs
// twice, then break L skips the `n += 100`).
func labeledSwitch(x uint64) uint64 {
	var n uint64
L:
	switch x {
	case 1:
		for k := uint64(0); k < 5; k++ {
			n++
			if n == 2 {
				break L
			}
		}
		n += 100
	default:
		n = 50
	}
	return n
}

// labeledSelect: `break L` of a labeled select, from a for inside a case.
// Returns 2.
func labeledSelect() uint64 {
	ch := make(chan uint64, 1)
	ch <- 1
	var n uint64
L:
	select {
	case v := <-ch:
		for k := uint64(0); k < 5; k++ {
			n += v
			if n == 2 {
				break L
			}
		}
		n += 100
	}
	return n
}

// labeledTypeSwitch: `break L` of a labeled type switch, from a for inside a
// case. Returns 2 for a uint64, and 0 otherwise.
func labeledTypeSwitch(x any) uint64 {
	var n uint64
L:
	switch x.(type) {
	case uint64:
		for k := uint64(0); k < 5; k++ {
			n++
			if n == 2 {
				break L
			}
		}
		n += 100
	}
	return n
}

// rangeSliceLabeled: labeled range over a slice; continue L and break L from
// an inner for. Sums the elements before the first 0, skipping odd ones.
// Returns 2 + 4 = 6.
func rangeSliceLabeled() uint64 {
	s := []uint64{2, 3, 4, 0, 8}
	var sum uint64
L:
	for _, x := range s {
		for {
			if x == 0 {
				break L
			}
			if x%2 == 1 {
				continue L
			}
			sum += x
			break
		}
	}
	return sum
}

// rangeMapLabeled: labeled range over a map (in arbitrary order); continue L
// skips keys with even values. The result does not depend on the order.
// Returns 1 + 3 = 4.
func rangeMapLabeled() uint64 {
	m := map[uint64]uint64{1: 11, 2: 22, 3: 33}
	var sum uint64
L:
	for k, v := range m {
		for {
			if v%2 == 0 {
				continue L
			}
			break
		}
		sum += k
	}
	return sum
}

// rangeMapBreakLabeled: break L ends a labeled range over a map after the
// first entry, whichever it is. Returns 1.
func rangeMapBreakLabeled() uint64 {
	m := map[uint64]uint64{1: 11, 2: 22, 3: 33}
	var n uint64
L:
	for range m {
		for {
			n++
			break L
		}
	}
	return n
}

// rangeIntLabeled: labeled range over an int. For i in 0..4, counts j < i;
// i = 4 ends the loop. Returns 0 + 1 + 2 + 3 = 6.
func rangeIntLabeled() uint64 {
	var n uint64
L:
	for i := range 5 {
		for j := range 5 {
			if i == 4 {
				break L
			}
			if j == i {
				continue L
			}
			n++
		}
	}
	return n
}

// seq yields 0, 1, 2, ... below n, and counts the calls of yield in *calls.
// It has its own label L, which must not interfere with its callers' L.
func seq(n uint64, calls *uint64) func(func(uint64) bool) {
	return func(yield func(uint64) bool) {
	L:
		for i := uint64(0); i < n; i++ {
			*calls++
			if !yield(i) {
				break L
			}
		}
	}
}

// rangeFuncLabeled: labeled range over a function (range-over-func). For x in
// 0..9, continue L skips odd x, break L ends at x = 6, so the sum is 0+2+4 = 6
// and yield is called 7 times. Returns 6*100 + 7 = 607.
func rangeFuncLabeled() uint64 {
	var calls uint64
	var sum uint64
L:
	for x := range seq(10, &calls) {
		for {
			if x == 6 {
				break L
			}
			if x%2 == 1 {
				continue L
			}
			sum += x
			break
		}
	}
	return sum*100 + calls
}

// breakThroughRangeFunc: break L from inside a range-over-func, aimed at an
// outer labeled for: the inner loop's outcome must leave func.forRange as a
// labeled outcome. Outer iteration i counts the x < i (unlabeled break at
// x == i), except that i = 3 leaves both loops at x = 1.
// Returns 0 + 1 + 2 + 1 = 4.
func breakThroughRangeFunc() uint64 {
	var calls uint64
	var n uint64
L:
	for i := uint64(0); i < 10; i++ {
		for x := range seq(10, &calls) {
			if i == 3 && x == 1 {
				break L
			}
			if x == i {
				break
			}
			n++
		}
	}
	return n
}

// returnInLabeledLoop: return from inside an inner loop of a labeled loop,
// with a continue L that runs before it. Returns 23 (i = 2, j = 3).
func returnInLabeledLoop() uint64 {
L:
	for i := uint64(0); i < 10; i++ {
		for j := uint64(0); j < 10; j++ {
			if i*j == 6 {
				return i*10 + j
			}
			if j > i+1 {
				continue L
			}
		}
	}
	return 0
}

// closureAcrossContinue: a closure capturing the loop variable i, created just
// before continue L; each iteration has its own i (Go 1.22), and the post
// statement i++ changes the next iteration's copy, not the captured one.
// Odd i are captured. Returns 1 + 3 = 4.
func closureAcrossContinue() uint64 {
	var fs []func() uint64
L:
	for i := uint64(0); i < 4; i++ {
		for {
			if i%2 == 1 {
				fs = append(fs, func() uint64 { return i })
				continue L
			}
			break
		}
	}
	var sum uint64
	for _, f := range fs {
		sum += f()
	}
	return sum
}

// sameLabelNested: label L in a function and in a function literal inside it.
// The literal's continue L and break L target the literal's own loop; f
// returns 3 (j = 0, 1, 3). The outer continue L skips the n += 100 at i = 1.
// Returns 3*3 + 100*2 = 209.
func sameLabelNested() uint64 {
	var n uint64
L:
	for i := uint64(0); i < 3; i++ {
		f := func() uint64 {
			var m uint64
		L:
			for j := uint64(0); j < 5; j++ {
				for {
					if j == 2 {
						continue L
					}
					if j == 4 {
						break L
					}
					m++
					break
				}
			}
			return m
		}
		n += f()
		if i == 1 {
			continue L
		}
		n += 100
	}
	return n
}

// countPairs: counts the pairs j < i < n, with continue L ending each inner
// loop. Returns n*(n-1)/2, a property a proof can state for all n.
func countPairs(n uint64) uint64 {
	var c uint64
L:
	for i := uint64(0); i < n; i++ {
		for j := uint64(0); ; j++ {
			if j == i {
				continue L
			}
			c++
		}
	}
	return c
}

// miniPrintf: a reduced doPrintf (Go's fmt/print.go). Text is copied; a '%'
// is followed by any number of '-' flags (counted) and then, for a lower-case
// verb, the verb in upper case (continue formatLoop, skipping the inner post
// statement), or otherwise '!' (break simpleFormat, then the rest is text).
func miniPrintf(format string) (string, uint64) {
	var out []byte
	var flags uint64
	end := len(format)
formatLoop:
	for i := 0; i < end; {
		lasti := i
		for i < end && format[i] != '%' {
			i++
		}
		if i > lasti {
			out = append(out, format[lasti:i]...)
		}
		if i >= end {
			break
		}
		i++
	simpleFormat:
		for ; i < end; i++ {
			c := format[i]
			switch c {
			case '-':
				flags++
			default:
				if 'a' <= c && c <= 'z' {
					out = append(out, c-'a'+'A')
					i++
					continue formatLoop
				}
				break simpleFormat
			}
		}
		out = append(out, '!')
	}
	return string(out), flags
}

func testLabeledContinue() bool      { return labeledContinue() == 10 }
func testLabeledBreak() bool         { return labeledBreak() == 23 }
func testBreakLoopFromSwitch() bool  { return breakLoopFromSwitch() == 2 }
func testContinueNestedSwitch() bool { return continueFromNestedSwitch() == 3 }
func testLabeledSwitch() bool        { return labeledSwitch(1) == 2 && labeledSwitch(0) == 50 }
func testLabeledSelect() bool        { return labeledSelect() == 2 }
func testLabeledTypeSwitch() bool {
	return labeledTypeSwitch(uint64(1)) == 2 && labeledTypeSwitch("a") == 0
}
func testRangeSliceLabeled() bool     { return rangeSliceLabeled() == 6 }
func testRangeMapLabeled() bool       { return rangeMapLabeled() == 4 }
func testRangeMapBreakLabeled() bool  { return rangeMapBreakLabeled() == 1 }
func testRangeIntLabeled() bool       { return rangeIntLabeled() == 6 }
func testRangeFuncLabeled() bool      { return rangeFuncLabeled() == 607 }
func testBreakThroughRangeFunc() bool { return breakThroughRangeFunc() == 4 }
func testReturnInLabeledLoop() bool   { return returnInLabeledLoop() == 23 }
func testClosureAcrossContinue() bool { return closureAcrossContinue() == 4 }
func testSameLabelNested() bool       { return sameLabelNested() == 209 }
func testCountPairs() bool            { return countPairs(0) == 0 && countPairs(5) == 10 }

func testMiniPrintf() bool {
	s, flags := miniPrintf("x%-vy%3z%")
	return s == "xVy!3z!" && flags == 1
}
