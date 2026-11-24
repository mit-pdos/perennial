// The Go model of bytealg.CompareString (Perennial/Code/internal/bytealg.toml,
// [model]), spliced into compare_native.go in place of the real declaration.

package bytealg

// MODEL: CompareString(a, b) is -1, 0 or +1 as a is lexicographically less
// than, equal to or greater than b. Go's is runtime.cmpstring (through
// abigen_runtime_cmpstring), which is assembly; the model compares with Go's <
// and == on strings, which order strings bytewise lexicographically as
// cmpstring does.
func CompareString(a, b string) int {
	if a < b {
		return -1
	}
	if a == b {
		return 0
	}
	return 1
}
