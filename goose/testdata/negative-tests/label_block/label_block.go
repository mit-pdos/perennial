package label_block

// a label on a statement other than a for, range, switch or select statement
// can only be the target of a goto, and is not supported.

func f(n uint64) uint64 {
	if n > 0 {
		goto L
	}
	n = 1
L: // ERROR label on a statement other than for, range, switch or select
	n++
	return n
}
