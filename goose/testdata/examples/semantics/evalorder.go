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
