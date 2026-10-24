package modelcheck_copy

// A whole-struct copy between two memory places: gc copies it with a Move,
// which differs from the semantics' value semantics when the two sides
// partially overlap (docs/design/unsafe-memory.md, R4).

type meta struct{ a, b, c, d, e, f, g, h uint64 }

func copyMeta(dst, src *meta) {
	*dst = *src // ERROR modelcheck: copy of
}
