package iface_map_key

// A map literal converts its keys to the key type, here an interface.

type SB = struct {
	X int `json:"b"`
}

func f() map[any]int {
	return map[any]int{SB{1}: 1} // ERROR identity is lost in translation
}
