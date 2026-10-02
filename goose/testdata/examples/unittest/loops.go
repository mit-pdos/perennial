package unittest

// DoSomething is an impure function
func DoSomething(s string) {}

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

func conditionalInLoop() {
	for i := uint64(0); ; {
		if i < 3 {
			DoSomething("i is small")
		}
		if i > 5 {
			break
		}
		i = i + 1
		continue
	}
}

func conditionalInLoopElse() {
	for i := uint64(0); ; {
		if i > 5 {
			break
		} else {
			i = i + 1
			continue
		}
	}
}

func nestedConditionalInLoopImplicitContinue() {
	for i := uint64(0); ; {
		if i > 5 {
			if i > 10 {
				break
			}
		} else {
			i = i + 1
			continue
		}
	}
}

func ImplicitLoopContinue() {
	for i := uint64(0); ; {
		if i < 4 {
			i = 0
		}
	}
}

func ImplicitLoopContinue2() {
	for i := uint64(0); ; {
		if i < 4 {
			i = 0
			continue
		}
	}
}

func ImplicitLoopContinueAfterIfBreak(i uint64) {
	for {
		if i > 0 {
			break
		}
	}
}

func nestedLoops() {
	for i := uint64(0); ; {
		for j := uint64(0); ; {
			if true {
				break
			}
			j = j + 1
			continue
		}
		i = i + 1
		continue
	}
}

func nestedGoStyleLoops() {
	for i := uint64(0); i < 10; i++ {
		for j := uint64(0); j < i; j++ {
			if true {
				break
			}
			// TODO: this is necessary to make the break actually return
			continue
		}
	}
}

func sumSlice(xs []uint64) uint64 {
	var sum uint64
	for _, x := range xs {
		sum += x
	}
	return sum
}

func intSliceLoop(xs []uint64) uint64 {
	var sum uint64
	for i := 0; i < len(xs); i++ {
		sum += xs[i]
	}
	return sum
}

func breakFromLoop() {
	for {
		if true {
			break
		}
		// TODO: this is necessary for the break to work
		continue
	}
}
