package iface_typeparam_embedded_literal

// A composite literal whose type is a type parameter with an embedded
// constraint converts its elements to the core type's element type, here an
// interface.

type SB = struct {
	X int `json:"b"`
}

type AnySlice interface{ ~[]any }

func mk[C interface{ AnySlice }]() C {
	return C{SB{1}} // ERROR identity is lost in translation
}
