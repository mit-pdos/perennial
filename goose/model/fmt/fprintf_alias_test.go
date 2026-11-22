package fmt_test

// The evidence for the model of fmt.Fprintf (Perennial/TrustedCode/fmt.lean, Fprintf.impl): gc
// hands Write its printer's pooled buffer, not a copy of the formatted bytes. Its spare capacity
// holds what earlier prints left there, and a writer that keeps the slice past the call sees it
// overwritten by a later print. The model hands Write a slice whose spare capacity holds arbitrary
// bytes (printerBuf), so gc's contents are among the model's outcomes, and after Write returns it
// leaves every cell of that slice, up to its capacity, with a write begun and never finished
// (retire), so that any later access through a kept slice is stuck: less defined than Go there,
// never different.

import (
	"fmt"
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
