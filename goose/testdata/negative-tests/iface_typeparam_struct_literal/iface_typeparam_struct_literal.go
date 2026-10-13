package iface_typeparam_struct_literal

// A struct literal whose type is a type parameter with a multi-term
// constraint converts its fields to the core type's field types, here an
// interface.

type SB = struct {
	X int `json:"b"`
}

type Box struct{ V any }
type Box2 struct{ V any }

func mk[B interface{ Box | Box2 }]() B {
	return B{V: SB{1}} // ERROR identity is lost in translation
}
