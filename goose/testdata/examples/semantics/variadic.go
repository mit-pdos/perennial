package semantics

func variadicSum(base uint64, xs ...uint64) uint64 {
	if xs == nil {
		return base + 1000
	}
	for _, x := range xs {
		base += x
	}
	return base
}

func variadicTriple() (uint64, uint64, uint64) {
	return 1, 2, 3
}

func variadicSingle() uint64 {
	return 5
}

type variadicSlice []uint64

func testVariadicCall() bool {
	s := []uint64{4, 5}
	var ns variadicSlice = s
	var empty []uint64
	return variadicSum(1) == 1001 &&
		variadicSum(1, 2, 3) == 6 &&
		variadicSum(1, s...) == 10 &&
		variadicSum(1, ns...) == 10 &&
		variadicSum(1, empty...) == 1001 &&
		variadicSum(1, nil...) == 1001 &&
		variadicSum(variadicTriple()) == 6 &&
		variadicSum(variadicSingle()) == 1005
}

func variadicSet(xs ...uint64) {
	xs[0] = 9
}

func testVariadicSliceAliases() bool {
	s := []uint64{1, 2}
	variadicSet(s...)
	return s[0] == 9
}

func variadicSend(ch chan uint64, xs ...uint64) {
	n := 100 * uint64(len(xs))
	for _, x := range xs {
		n += x
	}
	ch <- n
}

func variadicChanPair(ch chan uint64) (chan uint64, uint64) {
	return ch, 7
}

func testGoVariadic() bool {
	ch := make(chan uint64)
	go variadicSend(ch)
	a := <-ch
	go variadicSend(ch, 1, 2)
	b := <-ch
	go variadicSend(variadicChanPair(ch))
	c := <-ch
	return a == 0 && b == 203 && c == 107
}
