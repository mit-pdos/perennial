package modeloverlay

import "github.com/goose-lang/primitive"

// MODEL: Counter keeps Go's field n and adds a lock, which Inc takes.
type Counter struct {
	mu primitive.Mutex
	n  uint64
}

// MODEL: Inc adds one under the lock, as atomically as Go's atomic add.
func (c *Counter) Inc() {
	c.mu.Lock()
	c.n = c.n + 1
	c.mu.Unlock()
}

// MODEL: the first init function, in its place (before the second).
//
//gomodel:replace init.0 "order = append(order, 1)"
func init() {
	if choose() {
		order = append(order, 1)
	} else {
		order = append(order, 1)
	}
}

// bump is an addition of the model: translated.
func bump(c *Counter) {
	c.Inc()
	c.Inc()
}

// choose is a primitive stub: trusted (its Go body is for gc builds only).
func choose() bool {
	return false
}

// unmodelled is an addition that names_only lists: translated names-only
// (its name, no body), although translate matches it.
func unmodelled() uint64 {
	panic("unreachable")
}
