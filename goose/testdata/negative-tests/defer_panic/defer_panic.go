package defer_panic

// `defer panic(..)` is not translated: the deferred chain drops the outcome of
// a deferred call, which would lose the panic.

func f() {
	defer panic("p") // ERROR defer of panic
}
