package multi_assign_copy

type big struct{ a, b, c int64 }

// gc copies the first pair in place, which an overlapping view would corrupt.
func swap(p, q *big) {
	*p, *q = *q, *p // ERROR multiple assignment that copies
}
