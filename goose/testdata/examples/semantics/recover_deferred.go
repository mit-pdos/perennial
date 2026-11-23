package semantics

// recover() called directly by a deferred function or method (not a function
// literal): Goose translates such a function F as F'deferred, which takes the
// cell recover() reads as a parameter, and `defer F(...)` calls it.

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

// methodRecover: a deferred method recovers 7 into the named result.
func methodRecover() (x uint64) {
	c := &catcher{}
	defer c.catch(&x)
	panic(uint64(7))
}

// catchTop is a top-level function that recovers a uint64 panic value into *res.
func catchTop(res *uint64) {
	if r := recover(); r != nil {
		*res = r.(uint64)
	}
}

// topRecover: a deferred top-level function recovers 8 into the named result.
func topRecover() (x uint64) {
	defer catchTop(&x)
	panic(uint64(8))
}

// catchAndRepanic recovers, counts, and panics again with the value plus one.
func (c *catcher) catchAndRepanic() {
	r := recover()
	c.seen++
	panic(r.(uint64) + 1)
}

func repanicInner(c *catcher) {
	defer c.catchAndRepanic()
	panic(uint64(5))
}

// repanic: a deferred method recovers 5 and panics with 6, which a deferred
// literal of the caller recovers: 6*10 + 1.
func repanic() (x uint64) {
	c := &catcher{}
	defer func() {
		x = recover().(uint64)*10 + c.seen
	}()
	repanicInner(c)
	return 0
}

// catchTwice recovers the panic it is deferred for (through its parameter),
// panics with the value plus one, and recovers that in its own deferred literal
// (through its own cell).
func (c *catcher) catchTwice(res *uint64) {
	defer func() {
		*res = recover().(uint64) * 10
	}()
	r := recover().(uint64)
	panic(r + 1)
}

// twoCells: 4 is recovered by catchTwice, and 5 by catchTwice's literal: 50.
func twoCells() (x uint64) {
	c := &catcher{}
	defer c.catchTwice(&x)
	panic(uint64(4))
}

func catchNil(isNil *bool) {
	*isNil = recover() == nil
}

// recoverNotPanicking: a deferred function that recovers while nothing is
// panicking gets nil, and the function returns normally.
func recoverNotPanicking() (isNil bool) {
	defer catchNil(&isNil)
	return false
}

func testMethodRecover() bool       { return methodRecover() == 7 }
func testTopRecover() bool          { return topRecover() == 8 }
func testRepanic() bool             { return repanic() == 61 }
func testTwoCells() bool            { return twoCells() == 50 }
func testRecoverNotPanicking() bool { return recoverNotPanicking() }
