package semantics

// fallthrough, and break in switch and select statements

func fallthroughSwitch(x uint64) uint64 {
	var r uint64
	switch x {
	case 0:
		r += 1
		fallthrough
	case 1:
		r += 10
	case 2:
		r += 100
		fallthrough
	default:
		r += 1000
	case 3:
		fallthrough
	case 4:
		r += 10000
	}
	return r
}

func testFallthrough() bool {
	return fallthroughSwitch(0) == 11 &&
		fallthroughSwitch(1) == 10 &&
		fallthroughSwitch(2) == 1100 &&
		fallthroughSwitch(3) == 10000 &&
		fallthroughSwitch(4) == 10000 &&
		fallthroughSwitch(5) == 1000
}

// a body that returns does not fall through
func testFallthroughReturn() bool {
	x := uint64(0)
	switch x {
	case 0:
		if x == 0 {
			return true
		}
		fallthrough
	case 1:
		return false
	}
	return false
}

// break ends the switch, not the loop around it
func testBreakSwitch() bool {
	var n uint64
	for i := uint64(0); i < 3; i++ {
		switch i {
		case 1:
			break
		default:
			if i == 2 {
				break
			}
		}
		n += 1
	}
	return n == 3
}

// break in a loop in a switch ends the loop
func testBreakLoopInSwitch() bool {
	var n uint64
	switch {
	default:
		for {
			n += 1
			break
		}
		n += 1
	}
	return n == 2
}

// a fallthrough into a case body that breaks
func testFallthroughBreak() bool {
	var n uint64
	for i := uint64(0); i < 2; i++ {
		switch i {
		case 0:
			n += 1
			fallthrough
		case 1:
			if i == 0 {
				break
			}
			n += 10
		}
		n += 100
	}
	return n == 211
}

func testBreakTypeSwitch() bool {
	var n uint64
	var x interface{} = n
	for i := uint64(0); i < 2; i++ {
		switch x.(type) {
		case uint64:
			break
		}
		n += 1
	}
	return n == 2
}

func testBreakSelect() bool {
	c := make(chan uint64, 1)
	var n uint64
	for i := uint64(0); i < 2; i++ {
		c <- i
		select {
		case v := <-c:
			if v == 0 {
				break
			}
			n += 10
		}
		n += 1
	}
	return n == 12
}

// an empty block does not end the statements after it
func testEmptyBlock() bool {
	x := false
	{
	}
	x = true
	return x
}
