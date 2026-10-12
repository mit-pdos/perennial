package recover_indirect

// recover() is supported only directly in a function literal deferred by a
// defer statement.

func helper() {
	recover() // ERROR recover() is supported only directly in a function literal deferred by a defer statement
}

func f() {
	defer helper()
	panic("p")
}
