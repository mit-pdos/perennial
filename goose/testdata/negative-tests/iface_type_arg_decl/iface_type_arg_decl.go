package iface_type_arg_decl

// An instantiation in a type declaration (here a struct field) is checked as
// any other: inside G's methods T becomes a dynamic type, and the literal
// interface would be the same term as error.

type SA = []interface{ Error() string }

type G[T any] struct{ v T }

func (g G[T]) Get(x any) T { return x.(T) }

type H struct{ g G[SA] }

func (h H) M(x any) { h.g.Get(x) } // ERROR identity is lost in translation
