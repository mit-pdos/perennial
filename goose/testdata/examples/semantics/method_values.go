package semantics

// A method value x.M saves its receiver when it is evaluated (for a value
// receiver, a copy of it), and its calls use the saved receiver.

type mvBox struct {
	x uint64
}

func (b mvBox) get() uint64 {
	return b.x
}

func (b *mvBox) getPtr() uint64 {
	return b.x
}

type mvOuter struct {
	mvBox
}

type mvOuterPtr struct {
	*mvBox
}

func testMethodValueCopiesReceiver() bool {
	b := mvBox{x: 1}
	f := b.get
	b.x = 2
	return f() == 1
}

func testMethodValuePointerReceiver() bool {
	b := mvBox{x: 1}
	f := b.getPtr // (&b).getPtr
	b.x = 2
	return f() == 2
}

func testMethodValueThroughPointer() bool {
	p := &mvBox{x: 1}
	f := p.get // (*p).get: copies *p now
	p.x = 2
	return f() == 1
}

func testMethodValueEmbedded() bool {
	o := mvOuter{mvBox: mvBox{x: 1}}
	f := o.get // o.mvBox.get
	o.x = 2
	return f() == 1
}

func testMethodValueEmbeddedPointer() bool {
	o := mvOuterPtr{mvBox: &mvBox{x: 1}}
	f := o.get // (*o.mvBox).get
	o.x = 2
	g := o.getPtr // o.mvBox.getPtr: saves the pointer o.mvBox
	o.mvBox = &mvBox{x: 5}
	return f() == 1 && g() == 2
}

func mvDeferGet(out *uint64) {
	b := mvBox{x: 1}
	defer func(f func() uint64) { *out = f() }(b.get)
	b.x = 2
}

func mvDeferMethod(out *uint64) {
	b := mvBox{x: 1}
	defer b.store(out)
	b.x = 2
}

func (b mvBox) store(out *uint64) {
	*out = b.x
}

func testMethodValueDefer() bool {
	var out uint64
	mvDeferMethod(&out)
	return out == 1
}

func testMethodValueDeferArg() bool {
	var out uint64
	mvDeferGet(&out)
	return out == 1
}
