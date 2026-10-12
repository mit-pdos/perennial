package panic_post

// A `panic(..)` for post statement is not translated: doFor runs the post
// statement under `do:`, which would drop the panic.

func f() {
	for i := 0; i < 2; panic("post") { // ERROR panic in a for post statement
		i++
	}
}
