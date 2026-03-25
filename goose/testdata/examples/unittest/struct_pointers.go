package unittest

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

func (s *S) writeB(two TwoInts) {
	s.b = two
}

func (s *S) negateC() {
	s.c = !s.c
}

func (s *S) refC() *bool {
	return &s.c
}

func localSRef() *TwoInts {
	// this is all modeled correctly because if local variables escape Go
	// allocates them on the heap; we model stack variables linearly but can
	// optionally switch to a heavier-weight but more flexible heap-based model
	var s S
	return &s.b
}

func setField() S {
	var s S
	s.a = 0
	s.c = true
	return s
}
