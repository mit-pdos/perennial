// unittest has two package comments
package unittest

import "github.com/goose-lang/std"

// Note that compiling this test in Coq relies on the external marshal package
// being compiled and available.

type wrapExternalStruct struct {
	j *std.JoinHandle
}

func (w wrapExternalStruct) join() {
	w.j.Join()
}
