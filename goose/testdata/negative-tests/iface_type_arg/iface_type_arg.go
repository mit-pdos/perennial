package iface_type_arg

// A type argument may become a dynamic type inside the generic code, so it
// must keep its identity: here the two tagged structs would be one type.

type SA = struct {
	X int `json:"a"`
}

func as[T any](x any) T { return x.(T) }

func f() SA {
	var e any = 0
	return as[SA](e) // ERROR identity is lost in translation
}
