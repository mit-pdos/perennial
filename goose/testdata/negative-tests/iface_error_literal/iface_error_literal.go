package iface_error_literal

// error is a defined type, distinct from the literal interface with its
// method, but goose translates both as the same term.

func f() bool {
	var e any = []error{}
	_, ok := e.([]interface{ Error() string }) // ERROR identity is lost in translation
	return ok
}
