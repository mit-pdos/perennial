package unittest

// Implicit conversions from Go's assignability: a value assigned to a variable,
// field, element, parameter, result or channel of another type (a concrete type
// to an interface, an interface to a wider interface) is converted to it.

type assignT struct{ x uint64 }

type assignNarrow interface{ M() }

type assignWide interface {
	M()
	N()
}

func (t *assignT) M() {}
func (t *assignT) N() {}

func assignSelectSend(ch chan interface{}, p *assignT, done chan struct{}) {
	select {
	case ch <- p:
	case <-done:
	}
}

func assignSendPlain(ch chan interface{}, p *assignT) {
	ch <- p
}

func assignSelectSendIface(ch chan assignNarrow, w assignWide, done chan struct{}) {
	select {
	case ch <- w:
	case <-done:
	}
}

func assignSendPlainIface(ch chan assignNarrow, w assignWide) {
	ch <- w
}

func assignReturn(p *assignT) interface{} {
	return p
}

func assignReturnIface(w assignWide) assignNarrow {
	return w
}

func assignReturnMulti(p *assignT, w assignWide) (interface{}, assignNarrow) {
	return p, w
}

func assignPair(p *assignT) (*assignT, assignWide) {
	return p, p
}

func assignReturnTuple(p *assignT) (interface{}, assignNarrow) {
	return assignPair(p)
}

type assignS struct {
	a interface{}
	b assignNarrow
}

func assignCompositeLits(p *assignT, w assignWide) {
	_ = assignS{a: p, b: w}
	_ = assignS{p, w}
	_ = map[interface{}]assignNarrow{p: w}
	_ = []interface{}{p, w}
	_ = [2]assignNarrow{w, p}
}

func assignElementStores(p *assignT, w assignWide, m map[interface{}]assignNarrow, s []interface{}, a *[2]assignNarrow) {
	m[p] = w
	s[0] = p
	a[1] = w
}

func assignTakes(x interface{}, n assignNarrow) {}

func assignTakesVariadic(xs ...interface{}) {}

func assignCallArgs(p *assignT, w assignWide) {
	assignTakes(p, w)
	assignTakesVariadic(p, w)
	assignTakes(assignPair(p))
}

func assignRange(ps []*assignT, ws map[*assignT]assignWide, ch chan *assignT) {
	var x interface{}
	var n assignNarrow
	for x, n = range ws {
	}
	for _, x = range ps {
	}
	for x = range ch {
	}
	var arr [2]*assignT
	for x, x = range &arr {
	}
	for x, x = range "ab" {
	}
	for x = range 3 {
	}
	var i32 int32
	for i32 = range 3 {
	}
	for x, n = range func(yield func(*assignT, assignWide) bool) {} {
	}
	_, _, _ = x, n, i32
}

func assignMulti(p *assignT, w assignWide) {
	var x interface{}
	var n assignNarrow
	x, n = p, w
	x, n = assignPair(p)
	_, _ = x, n
}

func assignCommaOk(m map[int]*assignT, ch chan *assignT, i interface{}) {
	var x interface{}
	var ok bool
	x, ok = m[0]
	x, ok = <-ch
	x, ok = i.(*assignT)
	_, _ = x, ok
}

func assignGoDefer(p *assignT, w assignWide) {
	go assignTakes(p, w)
	defer assignTakes(p, w)
	go assignTakesVariadic(p, w)
	defer assignTakesVariadic(p, w)
}

func assignSelectRecv(ch chan *assignT, wch chan assignWide) {
	var x interface{}
	var n assignNarrow
	var ok bool
	select {
	case x = <-ch:
	case n = <-wch:
	case x, ok = <-ch:
	case n, ok = <-wch:
	}
	_, _, _ = x, n, ok
}
