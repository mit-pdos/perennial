package semantics

// Method sets: a type assertion to an interface type succeeds exactly when the
// dynamic type's method set has every method of the interface, with the same
// signature. Each test checks one fact about method sets.

type msGetter interface {
	Get() uint64
}

type msSetter interface {
	Set(x uint64)
}

type msValRecv struct{ x uint64 }

func (v msValRecv) Get() uint64 { return v.x }

type msPtrRecv struct{ x uint64 }

func (p *msPtrRecv) Set(x uint64) { p.x = x }

// A method with a value receiver is in the method set of T.
func testMethodSetValueReceiver() bool {
	var i any = msValRecv{x: 1}
	_, ok := i.(msGetter)
	return ok
}

// The method set of *T includes the methods with a value receiver.
func testMethodSetPointerHasValueMethods() bool {
	var i any = &msValRecv{x: 1}
	_, ok := i.(msGetter)
	return ok
}

// The method set of T excludes the methods with a pointer receiver.
func testMethodSetValueLacksPointerMethods() bool {
	var i any = msPtrRecv{}
	_, ok := i.(msSetter)
	var j any = &msPtrRecv{}
	_, ok2 := j.(msSetter)
	return !ok && ok2
}

// A type without the method is not in the type set (as `*errors.errorString`
// has no `Is`).
func testMethodSetMissingMethod() bool {
	var i any = &msPtrRecv{}
	_, ok := i.(msGetter)
	return !ok
}

// A method with the right name but another signature does not count.
type msGetU32 struct{}

func (msGetU32) Get() uint32 { return 0 }

func testMethodSetWrongSignature() bool {
	var i any = msGetU32{}
	_, ok := i.(msGetter)
	return !ok
}

// A variadic parameter differs from a slice parameter.
type msVariadic struct{}

func (msVariadic) Put(xs ...uint64) {}

func testMethodSetVariadic() bool {
	var i any = msVariadic{}
	_, ok1 := i.(interface{ Put(xs ...uint64) })
	_, ok2 := i.(interface{ Put(xs []uint64) })
	return ok1 && !ok2
}

// A type with no methods: a basic type, and a defined type over it.
type msInt uint64

func (n msInt) Get() uint64 { return uint64(n) }

func testMethodSetBasicType() bool {
	var i any = uint64(3)
	_, ok1 := i.(msGetter)
	var j any = msInt(3)
	_, ok2 := j.(msGetter)
	return !ok1 && ok2
}

// Methods promoted from an embedded struct: S's value methods are promoted to
// T and *T; *S's methods only to *T.
type msEmbedVal struct {
	msValRecv
	msPtrRecv
}

func testMethodSetPromotedFromStruct() bool {
	var i any = msEmbedVal{}
	_, ok1 := i.(msGetter)
	_, ok2 := i.(msSetter)
	var j any = &msEmbedVal{}
	_, ok3 := j.(msSetter)
	return ok1 && !ok2 && ok3
}

// Embedding *S promotes *S's methods to T as well.
type msEmbedPtr struct {
	*msPtrRecv
}

func testMethodSetPromotedFromPointer() bool {
	var i any = msEmbedPtr{msPtrRecv: &msPtrRecv{}}
	_, ok := i.(msSetter)
	return ok
}

// Methods promoted from an embedded interface (as a gRPC server struct that
// embeds the service interface).
type msEmbedIface struct {
	msGetter
}

func testMethodSetPromotedFromInterface() bool {
	var i any = &msEmbedIface{msGetter: msValRecv{x: 2}}
	g, ok := i.(msGetter)
	return ok && g.Get() == 2
}

// An unnamed struct type has the methods promoted from its embedded fields.
func testMethodSetUnnamedStruct() bool {
	var i any = struct{ msValRecv }{msValRecv{x: 4}}
	g, ok := i.(msGetter)
	return ok && g.Get() == 4
}

// An interface that embeds another interface has the embedded interface's
// methods (as `io.ReadWriter`).
type msGetSetter interface {
	msGetter
	msSetter
}

type msBoth struct{ x uint64 }

func (b *msBoth) Get() uint64  { return b.x }
func (b *msBoth) Set(x uint64) { b.x = x }

func testMethodSetEmbeddedInterface() bool {
	var i any = &msBoth{}
	_, ok1 := i.(msGetSetter)
	var j any = &msPtrRecv{}
	_, ok2 := j.(msGetSetter)
	return ok1 && !ok2
}

// Asserting from one interface type to another.
func testMethodSetInterfaceToInterface() bool {
	var g msGetter = &msBoth{x: 5}
	s, ok := g.(msSetter)
	if !ok {
		return false
	}
	s.Set(6)
	return g.Get() == 6
}

// The method set of an instantiated generic type.
type msBox[T any] struct{ v T }

func (b msBox[T]) Get() T { return b.v }

func testMethodSetGeneric() bool {
	var i any = msBox[uint64]{v: 7}
	_, ok1 := i.(msGetter)
	var j any = msBox[uint32]{v: 7}
	_, ok2 := j.(msGetter)
	return ok1 && !ok2
}

// Methods promoted to an instantiated generic type's pointer type from its
// embedded fields (a struct with a pointer method, and an interface).
type msEmbedGeneric[T any] struct {
	msPtrRecv
	msGetter
	v T
}

func testMethodSetPromotedGeneric() bool {
	b := &msEmbedGeneric[uint64]{msGetter: msValRecv{x: 3}}
	var i any = b
	s, ok1 := i.(msSetter)
	g, ok2 := i.(msGetter)
	if !ok1 || !ok2 {
		return false
	}
	s.Set(4)
	return g.Get() == 3 && b.msPtrRecv.x == 4
}

// Embedding *S in an instantiated generic type promotes *S's methods to it.
type msEmbedGenericPtr[T any] struct {
	*msPtrRecv
	v T
}

func testMethodSetPromotedGenericPointer() bool {
	p := &msPtrRecv{}
	var i any = &msEmbedGenericPtr[uint64]{msPtrRecv: p}
	s, ok := i.(msSetter)
	if !ok {
		return false
	}
	s.Set(5)
	return p.x == 5
}

// Unexported methods are in the method set (as the generated gRPC code's
// `interface{ testEmbeddedByValue() }`).
type msHidden struct{}

func (msHidden) hidden() {}

func testMethodSetUnexported() bool {
	var i any = msHidden{}
	_, ok1 := i.(interface{ hidden() })
	var j any = msValRecv{}
	_, ok2 := j.(interface{ hidden() })
	return ok1 && !ok2
}

// A type switch with interface cases checks method sets too.
func testMethodSetTypeSwitch() bool {
	var i any = msValRecv{}
	switch i.(type) {
	case msSetter:
		return false
	case msGetter:
		return true
	}
	return false
}

// A failed assertion to an interface panics (the single-result form).
func testMethodSetAssertPanics() (ok bool) {
	defer func() {
		ok = recover() != nil
	}()
	var i any = msValRecv{}
	_ = i.(msSetter)
	return false
}

// Methods whose receivers rename the type's parameters.
type msRenamed[A, B any] struct{ b B }

func (r msRenamed[B, A]) Get() A { return r.b }

func (r *msRenamed[X, Y]) Set(v Y) { r.b = v }

func testMethodSetRenamedParams() bool {
	var i any = msRenamed[uint32, uint64]{b: 7}
	_, ok1 := i.(msGetter)
	var j any = msRenamed[uint64, uint32]{b: 7}
	_, ok2 := j.(msGetter)
	return ok1 && !ok2
}
