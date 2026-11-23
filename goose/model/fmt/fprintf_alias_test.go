package fmt_test

// The evidence for the model of fmt.Fprintf (Perennial/TrustedCode/fmt.lean, Fprintf.impl): gc
// hands Write its printer's pooled buffer, not a copy of the formatted bytes. Its spare capacity
// holds what earlier prints left there, and a writer that keeps the slice past the call sees it
// overwritten by a later print (unless the buffer is above 64 KiB, which pp.free drops, so that the
// next printer's buffer is nil and Write may get a nil slice). The model hands Write a slice whose spare capacity holds arbitrary
// bytes (printerBuf), so gc's contents are among the model's outcomes, and after Write returns it
// leaves every cell of that slice, up to its capacity, with a write begun and never finished
// (retire), so that any later access through a kept slice is stuck: less defined than Go there,
// never different.

import (
	"bytes"
	"fmt"
	"strings"
	"testing"
)

type peek struct{ spare string }

// Write keeps nothing: during the call, it reads its argument's spare capacity.
func (k *peek) Write(p []byte) (int, error) {
	k.spare = string(p[len(p):cap(p)])
	return len(p), nil
}

type nop struct{}

func (nop) Write(p []byte) (int, error) { return len(p), nil }

// TestFprintfSpareCapacity: the spare capacity of Write's argument holds an earlier print's
// bytes, which the model's arbitrary bytes allow.
func TestFprintfSpareCapacity(t *testing.T) {
	for try := 0; try < 10; try++ {
		fmt.Fprintf(nop{}, "secret-%d", 12345)
		k := &peek{}
		fmt.Fprintf(k, "hi")
		if k.spare != string(make([]byte, len(k.spare))) {
			return // gc's spare capacity is not zero: the model must not zero it
		}
	}
	t.Fatal("the spare capacity of Write's argument was always zero; gc no longer reuses the printer's buffer")
}

type keep struct{ p []byte }

// Write keeps its argument past the call.
func (k *keep) Write(p []byte) (int, error) {
	k.p = p
	return len(p), nil
}

// TestFprintfKeptSliceOverwritten: a slice Write kept is overwritten by a later print, where a
// copy would stay; in the model any access through it is stuck.
func TestFprintfKeptSliceOverwritten(t *testing.T) {
	for try := 0; try < 10; try++ {
		k := &keep{}
		fmt.Fprintf(k, "first")
		_ = fmt.Sprintf("second-%d", 99999)
		if string(k.p) != "first" {
			return // overwritten by the later Sprintf
		}
	}
	t.Fatal("the kept slice was never overwritten; gc no longer reuses the printer's buffer")
}

type nilcheck struct{ isNil bool }

func (k *nilcheck) Write(p []byte) (int, error) {
	k.isNil = p == nil
	return len(p), nil
}

// TestFprintfNilBuffer: after a print above 64 KiB (whose buffer pp.free drops), Fprintf with empty
// output hands Write a nil slice, which the model's printerBuf allows for an empty output.
func TestFprintfNilBuffer(t *testing.T) {
	for try := 0; try < 10; try++ {
		fmt.Fprintf(nop{}, "%s", strings.Repeat("x", 70000))
		k := &nilcheck{}
		fmt.Fprintf(k, "")
		if k.isNil {
			return
		}
	}
	t.Fatal("Write never got a nil slice; gc no longer drops large printer buffers")
}

type panickingError struct{}

func (panickingError) Error() string { panic("boom") }

type panickingStringer struct{}

func (panickingStringer) String() string { panic("boom") }

// TestMethodPanicRecovered is the evidence for callError and callString (visitArg): gc's printer
// recovers a panic of an argument's Error() or String() (catchPanic), prints it, and returns
// normally, so a program that would catch the panic itself goes on differently. The model is
// stuck there (notModelled) rather than letting the panic reach the caller.
func TestMethodPanicRecovered(t *testing.T) {
	var buf bytes.Buffer
	n, err := fmt.Fprintf(&buf, "%v %s", panickingError{}, panickingStringer{})
	if err != nil || n != buf.Len() || !strings.Contains(buf.String(), "PANIC=") {
		t.Fatalf("Fprintf = %d, %v, %q: gc no longer recovers the method's panic", n, err, buf.String())
	}
	for _, arg := range []any{panickingError{}, panickingStringer{}} {
		if !runModel(func() { modelFprintf(&buf, "%v", arg) }) {
			t.Fatalf("the model does not get stuck on a panicking method of %T", arg)
		}
		if !runModel(func() { modelSprintf("%s", arg) }) {
			t.Fatalf("the model's Sprintf does not get stuck on a panicking method of %T", arg)
		}
	}
}
