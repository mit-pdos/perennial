package semantics

// range loops over arrays, and local types

func testRangeArray() bool {
	a := [3]uint64{1, 2, 3}
	var sum uint64
	var keys uint64
	for i, x := range a {
		sum += x
		keys += uint64(i)
	}
	return sum == 6 && keys == 3
}

// the loop ranges over a copy of the array
func testRangeArrayCopy() bool {
	a := [3]uint64{1, 2, 3}
	var sum uint64
	for _, x := range a {
		a[2] = 10
		sum += x
	}
	return sum == 6 && a[2] == 10
}

// ... but not over a pointer to an array
func testRangeArrayPtr() bool {
	a := [3]uint64{1, 2, 3}
	var sum uint64
	for _, x := range &a {
		a[2] = 10
		sum += x
	}
	return sum == 13
}

func testRangeArrayKeys() bool {
	var a [4]bool
	var n uint64
	for i := range a {
		n += uint64(i)
	}
	for range a {
		n += 1
	}
	return n == 10
}

// with only the key, the elements (here, through a nil pointer) are not read
func testRangeArrayNilPtr() bool {
	var p *[2]uint64
	var n uint64
	for i := range *p {
		n += uint64(i)
	}
	for i := range p {
		n += uint64(i)
	}
	return n == 2
}

func testRangeArrayBreak() bool {
	a := [4]uint64{1, 2, 3, 4}
	var sum uint64
	for _, x := range a {
		if x == 2 {
			continue
		}
		if x == 4 {
			break
		}
		sum += x
	}
	return sum == 4
}

type localPair struct {
	a uint64
}

func testLocalType() bool {
	type pair struct {
		a uint64
		b uint64
	}
	type pairs []pair
	ps := pairs{{a: 1, b: 2}, {a: 3, b: 4}}
	var sum uint64
	for _, p := range ps {
		sum += p.a * p.b
	}
	return sum == 14 && localPair{a: 1}.a == 1
}

// ranging over an array literal (which is not allocated)
func sumArrayLit() uint64 {
	var sum uint64
	for i, x := range [3]uint64{1, 2, 3} {
		sum += x + uint64(i)
	}
	return sum
}

func testRangeArrayLit() bool {
	return sumArrayLit() == 9
}
