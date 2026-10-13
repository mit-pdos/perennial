package iface_typeparam_literal

// A composite literal whose type is a type parameter converts its elements
// to the core type's element type, here an interface.

type SB = struct {
	X int `json:"b"`
}

func mk[C ~[]any]() C {
	return C{SB{1}} // ERROR identity is lost in translation
}
