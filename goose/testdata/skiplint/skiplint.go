// Package skiplint is the input of TestSkipLint (skip_test.go): skipped
// initializers that store to package variables, directly or through the
// package's functions, and ones that do not.
package skiplint

var registry = map[string]int{}

var count uint64

func register(k string) int {
	registry[k] = len(registry)
	return bump()
}

func bump() int {
	count++
	return int(count)
}

// stores to registry and count, through register and bump
var A = register("a")

// stores nothing beyond its local
var B = func() int {
	x := 1
	x++
	return x
}()

func newC() *uint64 {
	v := uint64(1)
	return &v
}

// only allocates
var C = newC()
