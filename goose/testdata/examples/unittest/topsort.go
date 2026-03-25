package unittest

// Make sure that goose tracks dependencies and emits A's Coq definition before
// B's.

type B struct {
	a []A
}

type A struct {
}
