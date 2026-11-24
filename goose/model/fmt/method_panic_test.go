package fmt_test

// The evidence that the model printer's callError and callString (visitArg) may be stuck where an
// argument's method panics: gc's printer recovers the panic.

import (
	"bytes"
	"fmt"
	"strings"
	"testing"
)

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
