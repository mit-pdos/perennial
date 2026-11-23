// Package recovers holds examples of recover() inside a named function or a
// method called by defer, which goose must translate (and Perennial verify)
// once that is supported. Go's rule (spec, "Handling panics"): recover returns
// nil when the goroutine is not panicking or recover was not called directly
// by a deferred function. Each test* function returns true in Go.
package recovers

type catcher struct {
	seen uint64
}

// catch recovers a uint64 panic value into *res and counts it.
func (c *catcher) catch(res *uint64) {
	if r := recover(); r != nil {
		c.seen++
		*res = r.(uint64)
	}
}

// methodRecover: a deferred method recovers and returns the panic value
// through the named result. Returns 7.
func methodRecover() (x uint64) {
	c := &catcher{}
	defer c.catch(&x)
	panic(uint64(7))
}

// catchTop is a top-level function that recovers.
func catchTop(ok *bool) {
	if recover() != nil {
		*ok = true
	}
}

// topRecover: a deferred top-level function recovers. Returns true.
func topRecover() (ok bool) {
	defer catchTop(&ok)
	panic("boom")
}

// catchAndRepanic recovers, counts, and panics again with value+1.
func (c *catcher) catchAndRepanic() {
	r := recover()
	c.seen++
	panic(r.(uint64) + 1)
}

func repanicInner(c *catcher) {
	defer c.catchAndRepanic()
	panic(uint64(5))
}

// repanic: a deferred method recovers and re-panics; a deferred literal in the
// caller recovers the new value. Returns 6*10 + seen = 61.
func repanic() (x uint64) {
	c := &catcher{}
	defer func() {
		x = recover().(uint64)*10 + c.seen
	}()
	repanicInner(c)
	return 0
}

func catchNil(isNil *bool) {
	*isNil = recover() == nil
}

// recoverNotPanicking: a deferred function that recovers while nothing is
// panicking gets nil, and the function returns normally. Returns true.
func recoverNotPanicking() (isNil bool) {
	defer catchNil(&isNil)
	return false
}

// methodValueRecover: `f := c.catch; defer f(&x)`. Go recovers here (f is the
// deferred function), so returns 9. Under the plan's proposal A goose cannot
// see that f is a recovering function: the translation may be stuck (a
// non-deferred `catch` is stuck), but must not return as if recover gave nil.
func methodValueRecover() (x uint64) {
	c := &catcher{}
	f := c.catch
	defer f(&x)
	panic(uint64(9))
}

// directCall: calling a recovering method directly (not deferred) while not
// panicking; recover returns nil in Go. Returns true (x and seen unchanged).
func directCall() bool {
	var x uint64 = 3
	c := &catcher{}
	c.catch(&x)
	return x == 3 && c.seen == 0
}

// helperInDeferredLiteral: a deferred literal calls the recovering method,
// which is then not called directly by the deferred function, so its recover
// returns nil and the panic goes on; the outer deferred literal recovers it.
// Returns 100 + 1 = 101.
func helperInDeferredLiteral() (x uint64) {
	defer func() {
		if r := recover(); r != nil {
			x = 100 + r.(uint64)
		}
	}()
	func() {
		c := &catcher{}
		defer func() { c.catch(&x) }()
		panic(uint64(1))
	}()
	return 0
}

// The fmt shape: handleMethods / catchPanic (Go's fmt/print.go).

type pp struct {
	buf       []byte
	panicking bool
}

// catchPanic: as fmt's, without the nil-pointer case and printing the panic
// value only when it is a string.
func (p *pp) catchPanic(verb byte, method string) {
	if err := recover(); err != nil {
		if p.panicking {
			// nested panics
			panic(err)
		}
		p.buf = append(p.buf, "%!"...)
		p.buf = append(p.buf, verb)
		p.buf = append(p.buf, "(PANIC="...)
		p.buf = append(p.buf, method...)
		p.buf = append(p.buf, " method: "...)
		if s, ok := err.(string); ok {
			p.buf = append(p.buf, s...)
		}
		p.buf = append(p.buf, ')')
	}
}

type stringer interface {
	String() string
}

func (p *pp) handleMethods(arg any, verb byte) (handled bool) {
	if s, ok := arg.(stringer); ok {
		handled = true
		defer p.catchPanic(verb, "String")
		p.buf = append(p.buf, s.String()...)
		return
	}
	return false
}

type good struct{}

func (good) String() string { return "ok" }

type bad struct{}

func (bad) String() string { panic("oops") }

// printArg returns handleMethods' result and the buffer.
func printArg(arg any, panicking bool) (bool, string) {
	p := &pp{panicking: panicking}
	h := p.handleMethods(arg, 'v')
	return h, string(p.buf)
}

// nestedPanic: with p.panicking set, catchPanic re-panics with the same value,
// which the caller's deferred literal recovers. Returns "oops".
func nestedPanic() (msg string) {
	defer func() {
		msg = recover().(string)
	}()
	printArg(bad{}, true)
	return ""
}

func testMethodRecover() bool           { return methodRecover() == 7 }
func testTopRecover() bool              { return topRecover() }
func testRepanic() bool                 { return repanic() == 61 }
func testRecoverNotPanicking() bool     { return recoverNotPanicking() }
func testMethodValueRecover() bool      { return methodValueRecover() == 9 }
func testDirectCall() bool              { return directCall() }
func testHelperInDeferredLiteral() bool { return helperInDeferredLiteral() == 101 }

func testHandleMethodsGood() bool {
	h, s := printArg(good{}, false)
	return h && s == "ok"
}

func testHandleMethodsBad() bool {
	h, s := printArg(bad{}, false)
	return h && s == "%!v(PANIC=String method: oops)"
}

func testHandleMethodsNotStringer() bool {
	h, s := printArg(uint64(3), false)
	return !h && s == ""
}

func testNestedPanic() bool { return nestedPanic() == "oops" }
