// Package grovefile is an example of a program over Grove's grove_ffi
// (github.com/mit-pdos/gokv/grove_ffi): a file written and read back, and the
// timestamp counter read twice.
package grovefile

import (
	"github.com/mit-pdos/gokv/grove_ffi"
)

// Run writes a file, reads it back and checks the contents; then reads the
// TSC twice and checks that it did not decrease. It panics if a check fails.
func Run() {
	data := []byte("hello")
	grove_ffi.FileWrite("f", data)
	got := grove_ffi.FileRead("f")
	if len(got) != len(data) {
		panic("length")
	}
	for i := range data {
		if got[i] != data[i] {
			panic("contents")
		}
	}
	t1 := grove_ffi.GetTSC()
	t2 := grove_ffi.GetTSC()
	if t2 < t1 {
		panic("tsc")
	}
}
