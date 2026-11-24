package modelwhole

// MODEL: counter as in the real package.
type counter struct {
	n uint64
}

// MODEL: get as in the real package.
func (c counter) get() uint64 { return c.n }

// MODEL: inc as in the real package.
func (c *counter) inc() { c.n = c.n + 1 }

// MODEL: W as in the real package.
type W struct {
	counter
}

// MODEL: Get as in the real package.
func (w W) Get() uint64 { return w.get() }
