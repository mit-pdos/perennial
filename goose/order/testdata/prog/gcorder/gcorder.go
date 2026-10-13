// Package gcorder is not translated: perennial-order compiles it in the
// compiler's own order.
package gcorder

type T struct{ V int }

func (t *T) set() error { t.V = 1; return nil }

// Parse relies on gc evaluating the call before reading o, as
// crypto/x509.ParseOID does.
func Parse() (T, error) {
	var o T
	return o, o.set()
}
