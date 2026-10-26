package modelcheck_loaded_pointers

// Two places with one root, reached through two pointers loaded from memory:
// the pointers can point at overlapping views, so the copy is refused
// (docs/design/unsafe-memory.md, R4, the same-base exemption).

type meta struct{ a, b, c, d, e, f, g, h uint64 }

type twoPointers struct{ x, y *meta }

func copyVia(pr *twoPointers) {
	*pr.y = *pr.x // ERROR modelcheck: copy of
}
