package semantics

type AdderType = func(uint64) uint64
type MultipleArgsType = func(uint64, bool) uint64

func adder() AdderType {
	var sum = uint64(0)
	return func(x uint64) uint64 {
		sum += x
		return sum
	}
}

func testClosureBasic() bool {
	pos := adder()
	doub := adder()
	for i := uint64(0); i < 10; i++ {
		pos(i)
		doub(2 * i)
	}
	if pos(0) == 45 && doub(0) == 90 {
		return true
	}
	return false
}
