// The Go model of runtime.Frames.Next (Perennial/Code/runtime.toml, [model]),
// spliced into symtab.go in place of the real declaration.

package runtime

import "internal/gomodel"

// MODEL: ci.Next() is the next frame of the program counters ci.callers,
// symbolized through the binary's tables (findfunc, the inlining tree, the
// cgo symbolizer; goose: "inc or dec statement with unsupported type
// uintptr", symtab.go:131), and whether another one follows. Go reads and
// writes *ci, so a nil ci panics (nil dereference) and a concurrent call on
// the same Frames races; the model's load and store of ci.callers do both.
// The model leaves *ci unchanged, where Go advances it, which no caller
// observes (the fields are unexported). It does not read the words
// ci.callers points to, which Go does (ci.callers[0]): a concurrent write to
// them races in Go and not in the model, but Go reads them only to look them
// up (any value gives some frames, a garbage one is skipped), and the model's
// frames are arbitrary anyway, so no outcome of that race is missing.
// Every exported field of the frame and more is arbitrary, a superset of
// what Go returns (goose/model/runtime/callers_test.go: a nil Func for a frame
// of a function inlined into its caller, Function/File/Line of the call
// sites, the zero frame with more false once the frames are exhausted). A
// non-nil Func is new(Func): Func is zero-size, and the semantics allocates a
// zero-size value at an arbitrary non-null address that owns no memory, so
// two results can be equal or not and a proof can read nothing through it, as
// with Go's pointers into the binary's tables. startLine and Entry are
// arbitrary too; funcInfo stays zero (unexported, read only by the runtime).
func (ci *Frames) Next() (frame Frame, more bool) {
	ci.callers = ci.callers
	frame.PC = uintptr(gomodel.ChooseUint64())
	if gomodel.Choose() {
		frame.Func = new(Func)
	}
	frame.Function = gomodel.ChooseString()
	frame.File = gomodel.ChooseString()
	frame.Line = int(gomodel.ChooseUint64())
	frame.startLine = int(gomodel.ChooseUint64())
	frame.Entry = uintptr(gomodel.ChooseUint64())
	more = gomodel.Choose()
	return
}
