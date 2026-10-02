package unittest

func conditionalReturn(x bool) uint64 {
	if x {
		return 0
	}
	return 1
}

func alwaysReturn(x bool) uint64 {
	if x {
		return 0
	} else {
		return 1
	}
}

func alwaysReturnInNestedBranches(x bool) uint64 {
	if !x {
		if x {
			return 0
		} else {
			return 1
		}
	} else {
		// we can even have an empty else block
	}
	y := uint64(14)
	return y
}

func earlyReturn(x bool) {
	if x {
		return
	}
}

func conditionalAssign(x bool) uint64 {
	var y uint64
	if x {
		y = 1
	} else {
		y = 2
	}
	y += 1
	return y
}

func elseIf(x, y bool) uint64 {
	if x {
		return 0
	} else if y {
		return 1
	} else {
		return 2
	}
}

func ifStmtInitialization(x uint64) uint64 {
	f := func() uint64 {
		return x
	}

	if f(); x == 2 {
	} else if z := x; z == 1 {
	} else if y := 94; y == 30 {
	} else if z = 10; x == 30 {
	}

	if y := uint64(10); x == 0 {
		return y
	} else {
		return y - 1
	}
}
