// Package trustedinit has a trusted init function: its model, init.impl, runs
// in its place when the package is initialized, after the global variables.
package trustedinit

var x uint64 = 1

func init() {
	x = 2
}
