// The Go model of runtime.callers (Perennial/Code/runtime.toml, [model]),
// spliced into traceback.go in place of the real declaration.

package runtime

import "internal/gomodel"

// MODEL: callers(skip, pcbuf), which Callers calls: Go walks the calling
// goroutine's stack (getg, sys.GetCallerPC/GetCallerSP, compiler intrinsics
// with no Go body, and the unwinder over the binary's tables) and writes the
// return program counters of the frames after the first skip into pcbuf[0],
// pcbuf[1], ..., stopping at the end of the stack or of pcbuf, and returns how
// many it wrote (tracebackPCs writes pcBuf[n] only for n < len(pcBuf)). It
// cannot panic: a skip past the stack's depth, or negative, writes fewer
// entries or the whole buffer. The model writes some prefix of pcbuf with
// arbitrary words and returns its length, every n from 0 to len(pcbuf) (Go: n
// < len(pcbuf) when the stack is shallower, 0 when skip is past it,
// len(pcbuf) when the buffer is too short: goose/model/runtime/callers_test.go).
// It writes the cells one at a time, as Go does, so a concurrent access to
// pcbuf races in the model as in Go.
func callers(skip int, pcbuf []uintptr) int {
	n := 0
	for n < len(pcbuf) && gomodel.Choose() {
		pcbuf[n] = uintptr(gomodel.ChooseUint64())
		n++
	}
	return n
}
