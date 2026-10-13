package semantics

func testCompareSliceToNil() bool {
	s := make([]byte, 0)
	return s != nil
}

func testComparePointerToNil() bool {
	s := new(uint64)
	return s != nil
}

func testCompareNilToNil() bool {
	s := new(*uint64)
	return *s == nil
}

func testComparePointerWrappedToNil() bool {
	var s []byte
	s = make([]byte, 1)
	return s != nil
}

func testComparePointerWrappedDefaultToNil() bool {
	var s []byte
	return s == nil
}

func testInterfaceNilWithType() bool {
	// subtlety in Go: nil interface vs interface with a nil pointer in it are
	// different
	var isNil any = nil
	var notNil any = (*string)(nil)
	return isNil == nil && notNil != nil && isNil != notNil
}

type nilFieldInner struct {
	a uint64
}

func (s *nilFieldInner) setA() {
	s.a = 1
}

type nilFieldOuter struct {
	nilFieldInner
	z struct{}
}

// nilFieldRef takes the address of a field through a nil pointer, which is a
// run-time panic in Go (here recovered). The model makes it a stuck panic, so
// this test is not provable: the model is less defined than Go.
func nilFieldRef() (panicked bool) {
	defer func() {
		if recover() != nil {
			panicked = true
		}
	}()
	var p *nilFieldOuter
	_ = &p.nilFieldInner
	return false
}

// nilFieldRefZeroSize panics even though the field occupies no memory.
func nilFieldRefZeroSize() (panicked bool) {
	defer func() {
		if recover() != nil {
			panicked = true
		}
	}()
	var p *nilFieldOuter
	_ = &p.z
	return false
}

// nilPromotedMethod calls a promoted pointer-receiver method through a nil
// pointer to the embedding struct, which computes the address of the embedded
// field and panics.
func nilPromotedMethod() (panicked bool) {
	defer func() {
		if recover() != nil {
			panicked = true
		}
	}()
	var p *nilFieldOuter
	p.setA()
	return false
}

func testNilFieldRefPanics() bool {
	return nilFieldRef() && nilFieldRefZeroSize() && nilPromotedMethod()
}
