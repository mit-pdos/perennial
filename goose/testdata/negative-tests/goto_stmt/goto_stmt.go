package goto_stmt

// goto is not supported, even to a labeled for statement.

func f(n uint64) uint64 {
L:
	for n < 10 {
		n++
		if n == 5 {
			goto L // ERROR goto
		}
	}
	return n
}
