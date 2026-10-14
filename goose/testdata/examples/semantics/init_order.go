package semantics

var initOrder []uint64

func init() {
	initOrder = append(initOrder, 1)
}

func init() {
	initOrder = append(initOrder, 2)
}

func testInitOrder() bool {
	return len(initOrder) == 3 && initOrder[0] == 1 && initOrder[1] == 2 && initOrder[2] == 3
}
