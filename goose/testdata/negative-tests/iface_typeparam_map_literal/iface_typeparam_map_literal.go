package iface_typeparam_map_literal

// A map literal whose type is a type parameter with a multi-term constraint
// converts its keys to the core type's key type, here an interface.

type SB = struct {
	X int `json:"b"`
}

type AnyMap map[any]int

func mk[M interface{ map[any]int | AnyMap }]() M {
	return M{SB{1}: 1} // ERROR identity is lost in translation
}
