package fmt_test

// The harness of the differential tests (model_diff_test.go): model_test.go is the model printer of
// goose/model/overlay/fmt/printmodel.go, rewritten into this package (model_copy_test.go); here are
// the stand-ins for what it calls of the overlay's other file (print.go) and of internal/gomodel,
// and the model's errorf, Fprintf, Fprint and Printf, each the body of the overlay's replaced
// declaration (print.go) with Go's printer, which the tests cannot reach, left out.

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
	s, _, _ := doPrintf(format, a, false)
	return s
}

// modelErrorf is Go's Errorf over the model's errorf.
func modelErrorf(format string, a ...any) error {
	if len(a) == 0 && strings.IndexByte(format, '%') == -1 {
		return errors.New(format)
	}
	s, wrapped, unknown := doPrintf(format, a, true)
	return errorfResult(s, wrapped, unknown, a)
}

// modelFprintf is the model's Fprintf: Write gets the bytes doPrintf formats.
func modelFprintf(w io.Writer, format string, a ...any) (int, error) {
	s, _, _ := doPrintf(format, a, false)
	return w.Write([]byte(s))
}

// modelFprint is Go's Fprint over the model's pp.doPrint.
func modelFprint(w io.Writer, a ...any) (int, error) {
	for _, x := range a {
		visitArg(x, 'v', false, false)
	}
	return w.Write([]byte(chooseString()))
}

// modelPrintf is the model's Printf with a writer that discards (the tests compare the calls).
func modelPrintf(format string, a ...any) (int, error) {
	return modelFprintf(io.Discard, format, a...)
}
