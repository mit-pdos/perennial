package semantics

type TwoInts struct {
	x uint64
	y uint64
}

type S struct {
	a uint64
	b TwoInts
	c bool
}

func NewS() *S {
	return &S{
		a: 2,
		b: TwoInts{x: 1, y: 2},
		c: true,
	}
}

func (s *S) readA() uint64 {
	return s.a
}

func (s *S) readB() TwoInts {
	return s.b
}

func (s S) readBVal() TwoInts {
	return s.b
}

func (s *S) updateBValX(i uint64) {
	s.b.x = i
}

func (s *S) negateC() {
	s.c = !s.c
}

func testStructUpdates() bool {
	var ok = true
	ns := NewS()

	ok = ok && (ns.readA() == 2)
	var b1 = ns.readB()
	ok = ok && (b1.x == 1)
	ns.negateC()
	ok = ok && (ns.c == false)

	b1.x = 3
	var b2 = ns.readB()
	ok = ok && (b2.x == 1)

	var b3 = &ns.b
	ok = ok && b3.x == 1

	ns.updateBValX(4)
	// FIXME: this isn't translated yet
	ok = ok && (ns.readBVal().x == 4)
	return ok
}

func testNestedStructUpdates() bool {
	var ok = true

	var ns = NewS()
	ns.b.x = 5
	ok = ok && ns.b.x == 5

	ns = NewS()
	var p = &ns.b
	p.x = 5
	ok = ok && ns.b.x == 5

	ns = NewS()
	p = &ns.b
	ns.b.x = 5
	ok = ok && (*p).x == 5

	ns = NewS()
	p = &ns.b
	ns.b.x = 5
	ok = ok && p.x == 5

	return ok
}

func testStructConstructions() bool {
	var ok = true

	var p1 *TwoInts           // p1 == nil
	var p2 TwoInts            // p2 == TwoInts{0, 0}
	p3 := TwoInts{y: 0, x: 0} // p3 == TwoInts{0, 0}
	p4 := TwoInts{x: 0, y: 0} // p4 == TwoInts{0, 0}

	ok = ok && (p1 == nil)
	p1 = new(TwoInts) // p1 == &TwoInts{0, 0}

	ok = ok && (p2 == p3)
	ok = ok && (p3 == p4)
	ok = ok && (p4 == *p1)

	ok = ok && (&p4 != p1)
	return ok
}

func testIncompleteStruct() bool {
	var ok = true

	p1 := TwoInts{x: 0}
	ok = ok && (p1.y == 0)

	p2 := S{a: 2}
	ok = ok && (p2.b.x == 0)
	ok = ok && (p2.c == false)

	return ok
}

type StructWrap struct {
	i uint64
}

func testStoreInStructVar() bool {
	var p StructWrap = StructWrap{i: 0}
	p.i = 5
	return p.i == 5
}

func testStoreInStructPointerVar() bool {
	var p *StructWrap = new(StructWrap)
	p.i = 5
	return p.i == 5
}

func testStoreComposite() bool {
	p := new(TwoInts)
	*p = TwoInts{x: 3, y: 4}
	return (*p).y == 4
}

func testStoreSlice() bool {
	p := new([]uint64)
	s := make([]uint64, 3)
	*p = s
	return uint64(len(*p)) == uint64(3)
}

type StructWithFunc struct {
	fn func(uint64) uint64
}

func testStructFieldFunc() bool {
	a := new(StructWithFunc)
	a.fn = func(arg uint64) uint64 {
		return arg * 2
	}
	return (a.fn(10) == 20)
}
