package rangefunc_recover

// recover() in the body of a range over a function returns nil in Go, even in a
// deferred function literal: the body runs as the body of the yield function.

func f(seq func(yield func() bool)) {
	defer func() {
		for range seq {
			recover() // ERROR recover() is supported only directly in a function literal deferred by a defer statement
		}
	}()
	panic("p")
}
