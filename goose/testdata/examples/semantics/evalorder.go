package semantics

// helpers
type evalCounter struct {
	n   uint64
	buf []uint64
}

func (c *evalCounter) next() []uint64 {
	c.n = c.n + 1
	return c.buf
}

// The operand of a slice expression without a high bound is evaluated once.
func testSliceOperandOnce() bool {
	c := &evalCounter{buf: []uint64{1, 2, 3}}
	s := c.next()[1:]
	return c.n == 1 && len(s) == 2
}

// The index operands on the left of an assignment are evaluated before any
// assignment is carried out.
func testAssignLhsIndexFirst() bool {
	a := []uint64{0, 0}
	i := uint64(0)
	i, a[i] = 1, 9
	return i == 1 && a[0] == 9 && a[1] == 0
}

func testAssignLhsDerefFirst() bool {
	x := uint64(0)
	y := uint64(0)
	p := &x
	p, *p = &y, 5
	return x == 5 && y == 0 && p == &y
}

func testAssignLhsMapFirst() bool {
	m1 := make(map[uint64]uint64)
	m2 := make(map[uint64]uint64)
	m := m1
	k := uint64(1)
	m, k, m[k] = m2, 2, 7
	return m1[1] == 7 && len(m2) == 0 && k == 2 && len(m) == 0
}

func (c *evalCounter) ch(ch chan uint64) chan uint64 {
	c.buf = append(c.buf, 1)
	return ch
}

func (c *evalCounter) val() uint64 {
	c.buf = append(c.buf, 2)
	return 0
}

// A send case evaluates its channel before its value.
func testSelectSendOrder() bool {
	c := &evalCounter{}
	ch := make(chan uint64, 1)
	select {
	case c.ch(ch) <- c.val():
	}
	return len(c.buf) == 2 && c.buf[0] == 1 && c.buf[1] == 2
}

// x op= y evaluates the operands of x's index expression once.
func testOpAssignIndexOnce() bool {
	n := uint64(0)
	idx := func() uint64 {
		n++
		return 0
	}
	a := [2]uint64{1, 1}
	a[idx()] += 2
	return n == 1 && a[0] == 3 && a[1] == 1
}

func testIncIndexOnce() bool {
	n := uint64(0)
	idx := func() uint64 {
		n++
		return 0
	}
	a := [2]uint64{1, 1}
	a[idx()]++
	return n == 1 && a[0] == 2 && a[1] == 1
}

func testOpAssignMapOnce() bool {
	n := uint64(0)
	idx := func() uint64 {
		n++
		return 0
	}
	m := make(map[uint64]uint64)
	m[0] = 5
	m[idx()] -= 2
	return n == 1 && m[0] == 3
}

// x op= y reads x after evaluating y.
func testOpAssignReadsAfterRhs() bool {
	x := uint64(1)
	f := func() uint64 {
		x = 100
		return 1
	}
	x += f()
	return x == 101
}

func testOpAssignMapReadsAfterRhs() bool {
	m := make(map[uint64]uint64)
	m[0] = 1
	f := func() uint64 {
		m[0] = 100
		return 1
	}
	m[0] += f()
	return m[0] == 101
}

// x++ is x += 1 at x's type, whatever its width.
func testIncDecNarrow() bool {
	var x int16 = 32767
	x++
	var y uint16 = 0
	y--
	return x == -32768 && y == 65535
}

func incGeneric[T ~uint8 | ~int16](x T) T {
	x++
	return x
}

func testIncGeneric() bool {
	return incGeneric(uint8(255)) == 0 && incGeneric(int16(1)) == 2
}

// x op= y reads the variables in x's operands after evaluating y, as gc does
// (and as for x = y).
func testOpAssignIndexReadAfterRhs() bool {
	a := [3]uint64{1, 2, 3}
	i := uint64(0)
	f := func() uint64 {
		i = 2
		return 1
	}
	a[i] += f()
	return a[0] == 1 && a[2] == 4
}

func testOpAssignMapReadAfterRhs() bool {
	m1 := make(map[uint64]uint64)
	m2 := make(map[uint64]uint64)
	m := m1
	f := func() uint64 {
		m = m2
		return 1
	}
	m[0] += f()
	return len(m1) == 0 && m2[0] == 1
}

// x[i] and x[lo:hi] read the variables in x after evaluating the calls in the
// index and the bounds, as gc does.
func testStringIndexReadAfterCall() bool {
	s := "abcdef"
	f := func() int {
		s = "xy"
		return 1
	}
	return s[f()] == 'y'
}

func testStringSliceReadAfterCall() bool {
	s := "abcdef"
	f := func() int {
		s = "xy"
		return 1
	}
	return s[f():] == "y"
}

func testSliceIndexReadAfterCall() bool {
	a := []uint64{1, 2, 3}
	f := func() int {
		a = []uint64{4, 5}
		return 1
	}
	return a[f()] == 5
}
