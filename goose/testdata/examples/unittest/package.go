// unittest has two package comments
package unittest

import "github.com/goose-lang/std"

// Note that compiling this test relies on the translation of the external std
// package being compiled and available.

type wrapExternalStruct struct {
	j *std.JoinHandle
}

func (w wrapExternalStruct) join() {
	w.j.Join()
}
