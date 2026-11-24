// The Go model of stringslite.Clone (Perennial/Code/internal/stringslite.toml,
// [model]), spliced into strings.go in place of the real declaration.

package stringslite

// MODEL: Clone(s) is a copy of s. Go's Clone ends in
// unsafe.String(&b[0], len(b)), which goose does not translate; the model is
// the same code with string(b) in its place, which returns a string with the
// same bytes (a copy of b, which nothing writes after the copy).
func Clone(s string) string {
	if len(s) == 0 {
		return ""
	}
	b := make([]byte, len(s))
	copy(b, s)
	return string(b)
}
