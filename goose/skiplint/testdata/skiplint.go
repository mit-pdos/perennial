// Package skiplint is the input of TestCheck (../skiplint_test.go): skipped
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

var tbl uint64

// stores to tbl through an alias: the address is flagged
func setTbl() uint64 {
	p := &tbl
	*p = 7
	return 0
}

var D = setTbl()
