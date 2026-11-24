// The Go model of strings.Compare (Perennial/Code/strings.toml, [model]),
// spliced into compare.go in place of the real declaration.

package strings

// MODEL: Compare(a, b) is -1, 0 or +1 as a is lexicographically less than,
// equal to or greater than b. Go's Compare is bytealg.CompareString, which is
// assembly (runtime.cmpstring); the model compares with Go's < and == on
// strings, which order strings bytewise lexicographically as cmpstring does.
func Compare(a, b string) int {
	if a < b {
		return -1
	}
	if a == b {
		return 0
	}
	return 1
}
