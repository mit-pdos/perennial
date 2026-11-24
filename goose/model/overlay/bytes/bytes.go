// The Go model of bytes.Compare (Perennial/Code/bytes.toml, [model]), spliced
// into bytes.go in place of the real declaration.

package bytes

// MODEL: Compare(a, b) is -1, 0 or +1 as a is lexicographically less than,
// equal to or greater than b (a nil slice is the empty one). Go's Compare is
// bytealg.Compare, which is assembly with no Go body (so the model is here,
// not in internal/bytealg: compare_amd64.s, which defines it, also defines
// runtime.cmpstring, so it cannot be blanked); the model compares the two slices' contents as strings, whose < is
// bytewise lexicographic, as Equal compares them with ==.
func Compare(a, b []byte) int {
	sa := string(a)
	sb := string(b)
	if sa < sb {
		return -1
	}
	if sa == sb {
		return 0
	}
	return 1
}
