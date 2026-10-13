package iface_error_typeparam

// interface{ Error() T } with T = string is identical to the literal interface
// of error, which goose translates as the same term as error.

func As[T any](x any) bool {
	_, ok := x.([]interface{ Error() T }) // ERROR identity is lost in translation
	return ok
}
