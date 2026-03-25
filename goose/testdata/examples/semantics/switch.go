package semantics

func testSwitchVal() bool {
	x := uint64(0)
	switch x {
	default:
		return false
	case 0:
		return true
	case 1:
		return false
	}
}

func testSwitchMultiple() bool {
	x := uint64(0)
	switch x {
	case 10, 1:
		return false
	case 0:
		return true
	}
	return false
}

func testSwitchDefaultTrue() bool {
	x := uint64(1)
	switch {
	case false:
		return false
	case x == 2:
		return false
	default:
		return true
	}
}

type switchConcrete struct {
}

type switchInterface interface {
	marker()
}

func (c *switchConcrete) marker() {
}

func testSwitchConversion() bool {
	v := &switchConcrete{}
	var x switchInterface = v
	switch x {
	case v:
	default:
		return false
	}

	switch v {
	case x:
	default:
		return false
	}
	return true
}
