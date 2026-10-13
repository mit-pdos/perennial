package iface_embedded_unexported

// An interface type is translated with its embedded interfaces flattened, so
// an embedded interface's unexported method appears in the term without the
// package that qualifies it in Go.

type hasM interface{ m() }

func f() any {
	return []interface{ hasM }{} // ERROR identity is lost in translation
}
