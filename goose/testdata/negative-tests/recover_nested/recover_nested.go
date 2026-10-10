package recover_nested

// a recover() in a function literal nested in the deferred one is not called
// directly by the deferred function.

func f() {
	defer func() {
		g := func() {
			recover() // ERROR recover() is supported only directly in a function literal deferred by a defer statement
		}
		g()
	}()
	panic("p")
}
