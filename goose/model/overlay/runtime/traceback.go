// The model of runtime.callers (Perennial/Code/runtime.toml), added to
// traceback.go: callers itself stays (gc runs the real stack walk, which
// testing.callerName and the like need), and is trusted, its GooseLang model
// (Perennial/TrustedCode/runtime.lean, callers.impl) a call of callersModel.

package runtime

import "internal/gomodel"

// MODEL: callersModel(skip, pcbuf) is the model of callers(skip, pcbuf), which
// Callers calls: Go walks the calling
// goroutine's stack (getg, sys.GetCallerPC/GetCallerSP, compiler intrinsics
// with no Go body, and the unwinder over the binary's tables) and writes the
// return program counters of the frames after the first skip into pcbuf[0],
// pcbuf[1], ..., stopping at the end of the stack or of pcbuf, and returns how
// many it wrote (tracebackPCs writes pcBuf[n] only for n < len(pcBuf)). It
// cannot panic: a skip past the stack's depth, or negative, writes fewer
// entries or the whole buffer. The model writes some prefix of pcbuf with
// arbitrary words and returns its length, every n from 0 to
// min(len(pcbuf), 2^40-1). The bound is the model assumption that a stack has
// fewer than 2^39 frames (README.md, "Model assumption (stack depth)";
// Perennial/TrustedCode/runtime.lean, callers.impl), so that a caller growing
// its buffer until it is not filled (zap's stacktrace.Capture) stops. (Go: n
// < len(pcbuf) when the stack is shallower, 0 when skip is past it,
// len(pcbuf) when the buffer is too short: goose/model/runtime/callers_test.go).
// It writes the cells one at a time, as Go does, so a concurrent access to
// pcbuf races in the model as in Go. (Not a replacement of callers: under gc,
// gomodel.Choose is false, so this body writes nothing, and the testing
// package panics when callers finds no frame.)
func callersModel(skip int, pcbuf []uintptr) int {
	n := 0
	for n < len(pcbuf) && n < 1<<40-1 && gomodel.Choose() {
		pcbuf[n] = uintptr(gomodel.ChooseUint64())
		n++
	}
	return n
}
