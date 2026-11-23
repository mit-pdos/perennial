package runtime

// Evidence for the models of runtime.callers and (*runtime.Frames).Next
// (Perennial/TrustedCode/runtime.lean): Callers writes a prefix of its buffer
// and returns its length, from 0 to len(pc); Next returns frames whose Func may
// be nil, and the zero frame with more false once they are exhausted.

import (
	"runtime"
	"testing"
)

const sentinel = ^uintptr(0)

func filled(n int) []uintptr {
	pc := make([]uintptr, n)
	for i := range pc {
		pc[i] = sentinel
	}
	return pc
}

// A shallow stack in a long buffer: n < len(pc), and the cells past n are not
// written.
func TestCallersWritesPrefix(t *testing.T) {
	pc := filled(1024)
	n := runtime.Callers(0, pc)
	if n <= 0 || n >= len(pc) {
		t.Fatalf("n = %d, want 0 < n < %d", n, len(pc))
	}
	for i := n; i < len(pc); i++ {
		if pc[i] != sentinel {
			t.Fatalf("pc[%d] written past n = %d", i, n)
		}
	}
}

// A buffer shorter than the stack: n == len(pc).
func TestCallersTruncates(t *testing.T) {
	pc := filled(1)
	if n := runtime.Callers(0, pc); n != 1 {
		t.Fatalf("n = %d, want 1", n)
	}
}

// A skip past the stack's depth, or an empty buffer: n == 0, nothing written.
func TestCallersZero(t *testing.T) {
	pc := filled(4)
	if n := runtime.Callers(1<<20, pc); n != 0 || pc[0] != sentinel {
		t.Fatalf("n = %d, pc[0] = %#x", n, pc[0])
	}
	if n := runtime.Callers(0, nil); n != 0 {
		t.Fatalf("n = %d for an empty buffer", n)
	}
	// a negative skip is not an error: the frames are recorded from Callers on
	if n := runtime.Callers(-3, filled(4)); n < 0 || n > 4 {
		t.Fatalf("n = %d for a negative skip", n)
	}
}

// callersHere is inlined into its caller (it is small and not marked noinline):
// its frame is a logical frame with no Func of its own.
func callersHere(pc []uintptr) int {
	return runtime.Callers(1, pc)
}

func TestFramesNext(t *testing.T) {
	pc := make([]uintptr, 64)
	n := callersHere(pc)
	frames := runtime.CallersFrames(pc[:n])
	sawNilFunc, sawFunc := false, false
	for {
		f, more := frames.Next()
		if f.Function == "" || f.File == "" || f.Line == 0 {
			t.Fatalf("frame without symbol information: %+v", f)
		}
		if f.Func == nil {
			sawNilFunc = true
		} else {
			sawFunc = true
		}
		if !more {
			break
		}
	}
	if !sawNilFunc || !sawFunc {
		t.Fatalf("want frames with and without Func: nil %v, non-nil %v", sawNilFunc, sawFunc)
	}
	// exhausted: the zero frame, more false
	if f, more := frames.Next(); more || f != (runtime.Frame{}) {
		t.Fatalf("after the last frame: %+v, %v", f, more)
	}
}
