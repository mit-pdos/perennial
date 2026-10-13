package iface_composite_elem

// A composite literal converts each element to its slot's type; for an
// interface slot the element's type becomes a dynamic type.

func f() []any {
	return []any{struct{ x int }{1}} // ERROR identity is lost in translation
}
