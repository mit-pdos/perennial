package semantics

// helpers
func standardForLoop(s []uint64) uint64 {
	// this is the boilerplate needed to do a normal for loop
	sumPtr := new(uint64)
	for i := uint64(0); ; {
		if i < uint64(len(s)) {
			// the body of the loop
			sum := *sumPtr
			x := s[i]
			*sumPtr = sum + x

			i = i + 1
			continue
		}
		break
	}
	sum := *sumPtr
	return sum
}

// based off diskAppendWait loop pattern in logging2
type LoopStruct struct {
	loopNext *uint64
}

func (ls LoopStruct) forLoopWait(i uint64) {
	for {
		nxt := ls.loopNext
		if i < *nxt {
			break
		}
		*ls.loopNext = *ls.loopNext + 1
		continue
	}
}

// tests
func testStandardForLoop() bool {
	var arr = make([]uint64, 4)
	arr[0] += 1
	arr[1] += 3
	arr[2] += 5
	arr[3] += 7
	return standardForLoop(arr) == 16
}

func testForLoopWait() bool {
	ls := LoopStruct{
		loopNext: new(uint64),
	}

	ls.forLoopWait(3)
	return (*ls.loopNext == 4)

}

func testBreakFromLoopWithContinue() bool {
	var i uint64 = 0
	for {
		if true {
			i = i + 1
			break
		}
		continue
	}
	return (i == 1)
}

func testBreakFromLoopNoContinue() bool {
	var i uint64 = 0
	for i < 3 {
		if true {
			i = i + 1
			break
		}
		i = i + 2
	}
	return (i == 1)
}

func testBreakFromLoopNoContinueDouble() bool {
	var i uint64 = 0
	for i < 3 {
		if i == 1 {
			i = i + 1
			break
		}
		i = i + 2
		i = i + 2
	}
	return (i == 4)
}

func testBreakFromLoopForOnly() bool {
	var i uint64 = 0
	for i < 3 {
		i = i + 2
	}
	return (i == 4)
}

func testBreakFromLoopAssignAndContinue() bool {
	var i uint64 = 0
	for i < 3 {
		if true {
			i = i + 1
			break
		}
		i = i + 2
		continue
	}
	return (i == 1)
}

func testNestedLoops() bool {
	var ok1 = false
	var ok2 = false
	for i := uint64(0); ; {
		for j := uint64(0); ; {
			if j > 5 {
				break
			}
			j = j + 1
			ok1 = j == 6
			continue
		}
		i = i + 1
		ok2 = (i == 1)
		break
	}
	return ok1 && ok2
}

func testNestedGoStyleLoops() bool {
	var ok = false
	for i := uint64(0); i < 10; i++ {
		for j := uint64(0); j < i; j++ {
			if true {
				break
			}
			continue
		}
		ok = i == 9
	}
	return ok
}

func testNestedGoStyleLoopsNoComparison() bool {
	var ok = false
	for i := uint64(0); i < 10; i++ {
		for j := uint64(0); j < i; j++ {
			if true {
				break
			}
			continue
		}
		ok = i == 9
	}
	return ok
}
