package runtime

// Evidence for the models of runtime.callers and (*runtime.Frames).Next
// (Perennial/TrustedCode/runtime.lean): Callers writes a prefix of its buffer
// and returns its length, from 0 to len(pc); a stack deeper than its limit is a
// fatal error, not a longer result (the model's bound on the frames); Next
// returns frames whose Func may be nil, and the zero frame with more false once
// they are exhausted.

import (
	"os"
	"os/exec"
	"runtime"
	"runtime/debug"
	"strings"
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

var depthSink int

func deep(n int) int {
	var pad [64]byte
	pad[n%64] = byte(n)
	return deep(n+1) + int(pad[0])
}

// A goroutine whose stack outgrows its limit is killed with a fatal error that
// recover does not catch ("goroutine stack exceeds ...-byte limit"), so no
// stack walk ever sees more frames than the limit holds.
func TestStackLimitFatal(t *testing.T) {
	if os.Getenv("CALLERS_STACK_CHILD") == "1" {
		debug.SetMaxStack(1 << 20)
		defer func() { recover(); os.Exit(0) }()
		depthSink = deep(0)
		return
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestStackLimitFatal$")
	cmd.Env = append(os.Environ(), "CALLERS_STACK_CHILD=1")
	out, err := cmd.CombinedOutput()
	if ee, ok := err.(*exec.ExitError); !ok || ee.ExitCode() == 0 {
		t.Fatalf("child exited %v; want a fatal error", err)
	}
	if !strings.Contains(string(out), "goroutine stack exceeds 1048576-byte limit") ||
		!strings.Contains(string(out), "fatal error: stack overflow") {
		t.Fatalf("child output:\n%s", out)
	}
}
