package recover_defer_recover

// a deferred function literal that calls recover() and itself defers a literal
// calling recover(): its recover() must stop the panic of f, which a
// `with_defer_recover:` of the literal would hide.

func f() (r int) {
	defer func() { // ERROR recover() in a deferred function literal that itself defers a function literal calling recover()
		defer func() { recover() }()
		if recover() != nil {
			r = 1
		}
	}()
	panic(5)
}
