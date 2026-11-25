package fmt_test

// The harness of the differential tests (model_diff_test.go): model_test.go is the model printer of
// goose/model/overlay/fmt/printmodel.go, rewritten into this package (model_copy_test.go); here are
// the stand-ins for what it calls of the overlay's other file (print.go) and of internal/gomodel,
// and the model's errorf, Fprintf, Fprint and printfFormat (the formatting of the trusted Printf),
// each the body of the overlay's declaration (print.go) with Go's printer, which the tests cannot
// reach, left out.

import (
	"errors"
	"fmt"
	"io"
	"reflect"
	"strings"
)

type State = fmt.State

// arbitraryMark stands for an arbitrary string in the model's output (chooseString).
const arbitraryMark = "\x00<arbitrary>\x00"

func chooseString() string { return arbitraryMark }

// arbitraryChoice is what gomodel.ChooseUint64() returns (arbitrary(); the tests run each choice).
var arbitraryChoice uint64

func arbitrary() uint64 { return arbitraryChoice }

// arbitraryBool is what gomodel.Choose() returns: false, so that writeArbitrary appends one
// arbitrary string (one arbitraryMark, which stands for any string, so for any number of them).
func arbitraryBool() bool { return false }

// buffer is fmt's printer buffer (print.go), with the method the model printer calls.
type buffer []byte

func (b *buffer) writeString(s string) { *b = append(*b, s...) }

// squash merges adjacent arbitraryMarks (the model's arbitrary strings appended one after
// another, which stand for any string together).
func squash(s string) string {
	for strings.Contains(s, arbitraryMark+arbitraryMark) {
		s = strings.ReplaceAll(s, arbitraryMark+arbitraryMark, arbitraryMark)
	}
	return s
}

type notModelledPanic struct{}

// notModelled stands for gomodel.Stuck() (no behaviour): the tests see a panic.
func notModelled() { panic(notModelledPanic{}) }

// underlyingAs is the overlay's primitive stub, with the same Go body.
func underlyingAs[T any](x any) (T, bool) {
	var z T
	if x == nil {
		return z, false
	}
	v := reflect.ValueOf(x)
	zt := reflect.TypeOf(z)
	if v.Kind() != zt.Kind() {
		return z, false
	}
	return v.Convert(zt).Interface().(T), true
}

type wrapError struct {
	msg string
	err error
}

func (e *wrapError) Error() string { return e.msg }
func (e *wrapError) Unwrap() error { return e.err }

type wrapErrors struct {
	msg  string
	errs []error
}

func (e *wrapErrors) Error() string   { return e.msg }
func (e *wrapErrors) Unwrap() []error { return e.errs }

// modelSprintf is a probe of the model printer's doPrintf, as a Sprintf (Sprintf itself is the
// real fmt's).
func modelSprintf(format string, a ...any) string {
	var b buffer
	doPrintf(&b, format, a, false)
	return squash(string(b))
}

// modelErrorf is Go's Errorf over the model's errorf (the printer's buffer a fresh one).
func modelErrorf(format string, a ...any) error {
	if len(a) == 0 && strings.IndexByte(format, '%') == -1 {
		return errors.New(format)
	}
	var b buffer
	wrapped, unknown := doPrintf(&b, format, a, true)
	return errorfResult(squash(string(b)), wrapped, unknown, a)
}

// modelFprintf is the model's Fprintf: Write gets the bytes doPrintf appends to a fresh buffer.
func modelFprintf(w io.Writer, format string, a ...any) (int, error) {
	var b buffer
	doPrintf(&b, format, a, false)
	return w.Write([]byte(squash(string(b))))
}

// modelFprint is Go's Fprint over the model's pp.doPrint.
func modelFprint(w io.Writer, a ...any) (int, error) {
	var b buffer
	for _, x := range a {
		writeArbitrary(&b)
		visitArg(x, 'v', false, false)
	}
	writeArbitrary(&b)
	return w.Write([]byte(squash(string(b))))
}

// modelFprintln is Go's Fprintln over the model's pp.doPrintln.
func modelFprintln(w io.Writer, a ...any) (int, error) {
	var b buffer
	for _, x := range a {
		writeArbitrary(&b)
		visitArg(x, 'v', false, false)
	}
	writeArbitrary(&b)
	return w.Write([]byte(squash(string(b))))
}

// modelPrintfFormat is printfFormat, the formatting of the trusted Printf (the tests compare the
// calls; the write to os.Stdout is not modelled).
func modelPrintfFormat(format string, a ...any) {
	var b buffer
	doPrintf(&b, format, a, false)
}
