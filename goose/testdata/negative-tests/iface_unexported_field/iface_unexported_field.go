package iface_unexported_field

// An unexported field name is qualified by its package in Go's type identity
// but not in goose's types, so `struct{ x int }` of two packages would be one
// type.

func f() any {
	return struct{ x int }{1} // ERROR its identity is lost in translation
}
