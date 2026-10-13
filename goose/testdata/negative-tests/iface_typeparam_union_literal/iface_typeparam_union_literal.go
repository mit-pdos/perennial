package iface_typeparam_union_literal

// A composite literal whose type is a type parameter with a multi-term
// constraint converts its elements to the core type's element type, here an
// interface.

type SB = struct {
	X int `json:"b"`
}

type Anys []any

func mk[C interface{ []any | Anys }]() C {
	return C{SB{1}} // ERROR identity is lost in translation
}
