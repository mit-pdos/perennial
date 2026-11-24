package fmt_test

// Differential tests of the model of fmt (model_test.go, the Go that the docstrings of
// Perennial/TrustedCode/fmt.lean quote) against Go's fmt: on every call the model does not get
// stuck on, its output matches Go's (each arbitrary string in it standing for any string), it
// calls exactly the methods Go calls, in the same order, and its Errorf returns an error of the
// same kind (errors.New, one wrapped error, several) wrapping the same errors. And on every call
// the specs admit (argsOk, a transcription of fmt.argsOk of Perennial/Proof/fmt/Base.lean), the
// model does not get stuck.

import (
	"errors"
	"fmt"
	"reflect"
	"strings"
	"testing"
)

// calls records the formatting methods called, in order.
var calls []string

type recErr struct{ s string }

func (e *recErr) Error() string { calls = append(calls, "Error:"+e.s); return "RE(" + e.s + ")" }

type valErr struct{ s string }

func (e valErr) Error() string { calls = append(calls, "vError:"+e.s); return "VE(" + e.s + ")" }

type recStr struct{ s string }

func (r *recStr) String() string { calls = append(calls, "String:"+r.s); return "RS(" + r.s + ")" }

// Both Error and String: Go calls Error.
type errStr struct{ s string }

func (e *errStr) Error() string  { calls = append(calls, "esError:"+e.s); return "ES(" + e.s + ")" }
func (e *errStr) String() string { calls = append(calls, "esString:"+e.s); return "ES2(" + e.s + ")" }

// A named integer with String (as raft's ConfChangeType, k8s's Decision).
type decision int

func (d decision) String() string { calls = append(calls, "decision"); return "D" }

// A named integer with Error.
type errCode int

func (c errCode) Error() string { calls = append(calls, "errCode"); return "EC" }

// A named integer and a named string without methods.
type plainInt int64

// Out of the specs: Format, GoString.
type fmter struct{}

func (fmter) Format(f fmt.State, c rune) { calls = append(calls, "Format"); f.Write([]byte("F")) }

type goStr struct{ s string }

func (g *goStr) GoString() string { calls = append(calls, "GoString"); return "G" }
func (g *goStr) String() string   { calls = append(calls, "gsString"); return "GS" }

// A pointer to a struct without methods.
type plainStruct struct{ a []int }

var testFormats = []string{
	"", "x", "%%", "%", "a%", "%v", "%s", "%d", "%x", "%X", "%q", "%w", "%T", "%p", "%#v", "%#w",
	"%+v", "%-5s", "%05d", "%016x", "%0d", "%00d", "%5%", "%v %v", "%s: %w", "%w %w", "%w, %v",
	"%d %s", "%v%", "%.3s", "%5.2v", "%*d", "%[1]v", "%[2]v %[1]v", "%01234567d", "%012345678d",
	"%.d", "%x.", "x%.", "%é", "%\xff", "%#x", "% d", "%+d", "%e", "%c", "%t", "%.5.d", "%v %d %s",
	"%-w", "%+w", "%v %v %v",
	// []byte: fmtBytes's verbs, with flags, width and precision the model does not follow
	"%#q", "%+q", "% x", "%#X", "%5s", "%.1s", "%#v", "%q %q", "%x %s",
}

// A named type of underlying type []byte: Go formats it by reflection (printValue), not by
// printArg's case []byte; the model does not follow it.
type namedBytes []byte

// A named type of underlying type []string: not the type []string itself, which the model
// follows; Go formats it as a []string (it has no methods), the model is stuck on it.
type namedStrings []string

func testArgs() []any {
	ps := &plainStruct{a: []int{1, 2}}
	return []any{
		nil, 7, -3, int8(-1), uint64(1 << 63), "str", plainName("pn"), plainInt(-12),
		true, 2.5, uintptr(9),
		&recErr{"a"}, valErr{"b"}, &recStr{"c"}, &errStr{"d"}, decision(2), errCode(3),
		stringerName("sn"), errorName("en"),
		fmter{}, &goStr{"g"}, ps, []byte("by"), []string{"x"},
		reflect.ValueOf(&recErr{"rv"}), reflect.Value{}, reflect.ValueOf(3),
		[]byte(nil), []byte{}, []byte("q\"b\\s\x00\x01\x1f\x7f\a\b\f\n\r\t\v ~"),
		[]byte("é"), []byte{0x80, 'a'}, []byte{0xff}, namedBytes("nb"),
		[]string(nil), []string{}, []string{"a", "b c", "", "é\x00\"%"}, namedStrings{"ns"},
	}
}

// bytesOk: the admission of lent slice arguments (fmt.argsOkB): argsOk, with an argument of type
// []byte or []string (exactly) also admitted under every directive, where the directives parse.
func bytesOk(mv, format string, a []any) bool {
	ds, ok := directives(format)
	if !ok {
		return argsOk(mv, format, a)
	}
	for k, x := range a {
		d := directive{'v', false}
		if k < len(ds) {
			d = ds[k]
		}
		if _, isB := x.([]byte); isB {
			continue
		}
		if _, isS := x.([]string); isS {
			continue
		}
		if !argOkAt(mv, d, x) {
			return false
		}
	}
	return true
}

// matches: whether got is one of the strings the pattern stands for, arbitraryMark standing for
// any string.
func matches(pattern, got string) bool {
	parts := strings.Split(pattern, arbitraryMark)
	if len(parts) == 1 {
		return pattern == got
	}
	if !strings.HasPrefix(got, parts[0]) {
		return false
	}
	rest := got[len(parts[0]):]
	for k := 1; k < len(parts)-1; k++ {
		j := strings.Index(rest, parts[k])
		if j < 0 {
			return false
		}
		rest = rest[j+len(parts[k]):]
	}
	return strings.HasSuffix(rest, parts[len(parts)-1])
}

// runModel runs f, reporting whether it got stuck (notModelled).
func runModel(f func()) (stuck bool) {
	defer func() {
		if r := recover(); r != nil {
			if _, ok := r.(notModelledPanic); ok {
				stuck = true
				return
			}
			panic(r)
		}
	}()
	f()
	return false
}

// The specs' premise (fmt.argsOk), transcribed.

type directive struct {
	verb   byte
	sharpV bool
}

// directives transcribes fmt.fmtDirectives.
func directives(format string) ([]directive, bool) {
	var ds []directive
	inDir, sharp, phase, n := false, false, 0, 0
	for i := 0; i < len(format); i++ {
		b := format[i]
		if !inDir {
			if b == '%' {
				inDir, sharp, phase, n = true, false, 0, 0
			}
			continue
		}
		digit := '0' <= b && b <= '9'
		verb := func() bool {
			if b == '*' || b == '[' {
				return false
			}
			inDir = false
			if b != '%' {
				ds = append(ds, directive{b, sharp && (b == 'v' || b == 'w')})
			}
			return true
		}
		switch phase {
		case 0:
			if b == '#' {
				sharp = true
			} else if b == '+' || b == '-' || b == '0' || b == ' ' {
			} else if digit {
				phase, n = 1, 1
			} else if b == '.' && i+1 < len(format) {
				phase, n = 2, 0
			} else if !verb() {
				return nil, false
			}
		case 1:
			if digit {
				if n >= 7 {
					return nil, false
				}
				n++
			} else if b == '.' && i+1 < len(format) {
				phase, n = 2, 0
			} else if !verb() {
				return nil, false
			}
		case 2:
			if digit {
				if n >= 7 {
					return nil, false
				}
				n++
			} else if !verb() {
				return nil, false
			}
		}
	}
	return ds, true
}

func hasMethod(x any, name string) bool {
	_, ok := reflect.TypeOf(x).MethodByName(name)
	return ok
}

// argWf transcribes fmt.ArgWf: a predeclared basic type, or a type of integer or string kind
// without any method named Format, GoString, Error or String.
func argWf(x any) bool {
	switch x.(type) {
	case bool, int, int8, int16, int32, int64, uint, uint8, uint16, uint32, uint64, uintptr,
		float32, float64, string:
		return true
	}
	for _, m := range []string{"Format", "GoString", "Error", "String"} {
		if hasMethod(x, m) {
			return false
		}
	}
	return isStrKind(x) || isIntKind(x)
}

func implementsError(x any) bool  { _, ok := x.(error); return ok }
func implementsString(x any) bool { _, ok := x.(fmt.Stringer); return ok }

func refKind(x any) bool {
	switch reflect.TypeOf(x).Kind() {
	case reflect.Pointer, reflect.Slice, reflect.Map, reflect.Chan, reflect.Func,
		reflect.UnsafePointer:
		return true
	}
	return false
}

// isReflectValue transcribes argOk's exclusion of reflect.Value: no method named CanInterface.
func isReflectValue(x any) bool { return hasMethod(x, "CanInterface") }

// argOkAt transcribes fmt.argOkAt.
func argOkAt(mv string, d directive, x any) bool {
	if x == nil || argWf(x) {
		return true
	}
	isMv := strings.IndexByte(mv, d.verb) >= 0
	if !isMv && isIntKind(x) && !hasMethod(x, "Format") &&
		(implementsError(x) || implementsString(x)) {
		return true
	}
	if d.verb == 'T' {
		return true
	}
	if d.verb == 'p' && refKind(x) {
		return true
	}
	if isMv && !d.sharpV && (d.verb != 'w' || implementsError(x)) {
		if implementsError(x) && !hasMethod(x, "Format") {
			return true
		}
		if implementsString(x) && !hasMethod(x, "Format") && !hasMethod(x, "Error") &&
			!isReflectValue(x) {
			return true
		}
	}
	return false
}

func argsOk(mv, format string, a []any) bool {
	ds, ok := directives(format)
	if !ok {
		for _, x := range a {
			if !(x == nil || argWf(x)) {
				return false
			}
		}
		return true
	}
	for k, x := range a {
		d := directive{'v', false}
		if k < len(ds) {
			d = ds[k]
		}
		if !argOkAt(mv, d, x) {
			return false
		}
	}
	return true
}

func argTuples() [][]any {
	args := testArgs()
	tuples := [][]any{{}}
	for _, x := range args {
		tuples = append(tuples, []any{x})
	}
	for _, x := range args {
		for _, y := range args {
			tuples = append(tuples, []any{x, y})
		}
	}
	for _, x := range []any{&recErr{"p"}, 5, "s"} {
		for _, y := range []any{&recErr{"q"}, decision(1), nil} {
			for _, z := range []any{&recStr{"r"}, -4, valErr{"t"}} {
				tuples = append(tuples, []any{x, y, z})
			}
		}
	}
	return tuples
}

func describe(format string, a []any) string {
	var b strings.Builder
	fmt.Fprintf(&b, "%q", format)
	for _, x := range a {
		fmt.Fprintf(&b, ", %T", x)
	}
	return b.String()
}

func TestModelSprintf(t *testing.T) {
	admitted, stuckN := 0, 0
	for _, format := range testFormats {
		for _, a := range argTuples() {
			calls = nil
			got := fmt.Sprintf(format, a...)
			goCalls := calls
			calls = nil
			var out string
			stuck := runModel(func() { out = modelSprintf(format, a...) })
			modelCalls := calls
			ok := bytesOk("vsxXq", format, a)
			if ok {
				admitted++
			}
			if stuck {
				stuckN++
				if ok {
					t.Errorf("Sprintf(%s): admitted, but the model is stuck", describe(format, a))
				}
				continue
			}
			if !matches(out, got) {
				t.Errorf("Sprintf(%s) = %q, the model's %q", describe(format, a), got, out)
			}
			if !reflect.DeepEqual(goCalls, modelCalls) {
				t.Errorf("Sprintf(%s): Go calls %v, the model %v", describe(format, a), goCalls,
					modelCalls)
			}
		}
	}
	t.Logf("%d calls admitted, %d where the model is stuck", admitted, stuckN)
}

func TestModelPrintf(t *testing.T) {
	for _, format := range testFormats {
		for _, a := range argTuples() {
			calls = nil
			_ = fmt.Sprintf(format, a...) // Printf formats as Sprintf does
			goCalls := calls
			calls = nil
			stuck := runModel(func() { modelPrintf(format, a...) })
			if stuck {
				continue
			}
			if !reflect.DeepEqual(goCalls, calls) {
				t.Errorf("Printf(%s): Go calls %v, the model %v", describe(format, a), goCalls,
					calls)
			}
		}
	}
}

// The model formats %s, %v, %d, %x, %X of a []byte exactly, and %q of one whose bytes are ASCII
// (every byte below 0x80 included, so every escape strconv.Quote prints of one); %q of a
// non-ASCII byte is an arbitrary string.
func TestModelBytesExact(t *testing.T) {
	var all []byte
	for c := 0; c < 0x80; c++ {
		all = append(all, byte(c))
	}
	ascii := [][]byte{nil, {}, []byte("plain"), all, []byte("q\"b\\s\x00\x7f\a\b\f\n\r\t\v")}
	for _, verb := range []string{"%s", "%v", "%d", "%x", "%X", "%q"} {
		for _, b := range ascii {
			format := "<" + verb + ">"
			got := fmt.Sprintf(format, b)
			out := modelSprintf(format, b)
			if out != got {
				t.Errorf("Sprintf(%q, %q) = %q, the model's %q", format, b, got, out)
			}
		}
	}
	for _, b := range [][]byte{[]byte("é"), {0x80}, {'a', 0xff}} {
		if out := modelSprintf("<%q>", b); out != "<"+arbitraryMark {
			t.Errorf("Sprintf(\"<%%q>\", %q): the model's %q, not arbitrary", b, out)
		}
	}
}

// The model formats %s and %v of a []string exactly, whatever its strings: brackets, the strings
// separated by spaces; its other directives (%q, %x, %d, flags, width) are arbitrary strings.
func TestModelStringsExact(t *testing.T) {
	cases := [][]string{nil, {}, {""}, {"", ""}, {"a"}, {"a", "b c", "é\x00\xff\"%", "[x]"},
		{"https://127.0.0.1:2379", "https://127.0.0.2:2379"}}
	for _, verb := range []string{"%s", "%v"} {
		for _, ss := range cases {
			format := "<" + verb + ">"
			got := fmt.Sprintf(format, ss)
			out := modelSprintf(format, ss)
			if out != got {
				t.Errorf("Sprintf(%q, %q) = %q, the model's %q", format, ss, got, out)
			}
		}
	}
	for _, format := range []string{"<%q>", "<%x>", "<%d>", "<%5s>", "<%+v>", "<%#v>"} {
		if out := modelSprintf(format, []string{"a"}); out != "<"+arbitraryMark {
			t.Errorf("Sprintf(%q, []string{\"a\"}): the model's %q, not arbitrary", format, out)
		}
	}
}

// recWriter records each Write: its bytes, as a call, then returns its fixed results.
type recWriter struct {
	writes [][]byte
	n      int
	err    error
}

func (w *recWriter) Write(p []byte) (int, error) {
	calls = append(calls, "Write")
	w.writes = append(w.writes, append([]byte(nil), p...))
	return w.n, w.err
}

// Fprintf: the same calls as Sprintf's formatting, then one Write of the formatted bytes (also
// when they are empty), returning what Write returns.
func TestModelFprintf(t *testing.T) {
	werr := errors.New("w")
	for _, format := range testFormats {
		for _, a := range argTuples() {
			for _, res := range []struct {
				n   int
				err error
			}{{3, nil}, {0, werr}} {
				calls = nil
				gw := &recWriter{n: res.n, err: res.err}
				gn, gerr := fmt.Fprintf(gw, format, a...)
				goCalls := calls
				calls = nil
				mw := &recWriter{n: res.n, err: res.err}
				var mn int
				var merr error
				stuck := runModel(func() { mn, merr = modelFprintf(mw, format, a...) })
				if stuck {
					if bytesOk("vsxXq", format, a) {
						t.Errorf("Fprintf(%s): admitted, but the model is stuck", describe(format, a))
					}
					continue
				}
				if !reflect.DeepEqual(goCalls, calls) {
					t.Errorf("Fprintf(%s): Go calls %v, the model %v", describe(format, a), goCalls,
						calls)
				}
				if len(gw.writes) != 1 || len(mw.writes) != 1 {
					t.Errorf("Fprintf(%s): Go writes %d times, the model %d", describe(format, a),
						len(gw.writes), len(mw.writes))
					continue
				}
				if !matches(string(mw.writes[0]), string(gw.writes[0])) {
					t.Errorf("Fprintf(%s) writes %q, the model %q", describe(format, a),
						gw.writes[0], mw.writes[0])
				}
				if gn != mn || gerr != merr {
					t.Errorf("Fprintf(%s) = %d, %v; the model's %d, %v", describe(format, a), gn,
						gerr, mn, merr)
				}
			}
		}
	}
}

// Fprint: the calls Go's printArg makes of each operand under %v, in order, then one Write (also
// when the output is empty), returning what Write returns; the output is arbitrary. Admitted (the
// spec's fmt.printArgOk): each operand as argOkAt admits it under %v.
func TestModelFprint(t *testing.T) {
	werr := errors.New("w")
	admitted := 0
	for _, a := range argTuples() {
		ok := true
		for _, x := range a {
			if !argOkAt("vsxXq", directive{'v', false}, x) {
				ok = false
			}
		}
		if ok {
			admitted++
		}
		for _, res := range []struct {
			n   int
			err error
		}{{3, nil}, {0, werr}} {
			calls = nil
			gw := &recWriter{n: res.n, err: res.err}
			gn, gerr := fmt.Fprint(gw, a...)
			goCalls := calls
			calls = nil
			mw := &recWriter{n: res.n, err: res.err}
			var mn int
			var merr error
			stuck := runModel(func() { mn, merr = modelFprint(mw, a...) })
			if stuck {
				if ok {
					t.Errorf("Fprint(%s): admitted, but the model is stuck", describe("", a))
				}
				continue
			}
			if !reflect.DeepEqual(goCalls, calls) {
				t.Errorf("Fprint(%s): Go calls %v, the model %v", describe("", a), goCalls, calls)
			}
			if len(gw.writes) != 1 || len(mw.writes) != 1 {
				t.Errorf("Fprint(%s): Go writes %d times, the model %d", describe("", a),
					len(gw.writes), len(mw.writes))
				continue
			}
			if !matches(string(mw.writes[0]), string(gw.writes[0])) {
				t.Errorf("Fprint(%s) writes %q, the model %q", describe("", a), gw.writes[0],
					mw.writes[0])
			}
			if gn != mn || gerr != merr {
				t.Errorf("Fprint(%s) = %d, %v; the model's %d, %v", describe("", a), gn, gerr, mn,
					merr)
			}
		}
	}
	t.Logf("%d operand lists admitted", admitted)
}

// errKind: 0 for an *errors.errorString, 1 for a *fmt.wrapError, 2 for a *fmt.wrapErrors, and
// what it wraps.
func errKind(err error) (int, []error) {
	switch e := err.(type) {
	case *wrapError:
		return 1, []error{e.err}
	case *wrapErrors:
		return 2, e.errs
	}
	switch reflect.TypeOf(err).String() {
	case "*errors.errorString":
		return 0, nil
	case "*fmt.wrapError":
		return 1, []error{errors.Unwrap(err)}
	case "*fmt.wrapErrors":
		return 2, err.(interface{ Unwrap() []error }).Unwrap()
	}
	return -1, nil
}

func TestModelErrorf(t *testing.T) {
	for _, format := range testFormats {
		for _, a := range argTuples() {
			calls = nil
			gerr := fmt.Errorf(format, a...)
			goCalls := calls
			gk, gw := errKind(gerr)
			ok := bytesOk("vsxXqw", format, a)
			var found bool
			for choice := uint64(0); choice < 3; choice++ {
				arbitraryChoice = choice
				calls = nil
				var merr error
				stuck := runModel(func() { merr = modelErrorf(format, a...) })
				if stuck {
					if ok {
						t.Errorf("Errorf(%s): admitted, but the model is stuck", describe(format, a))
					}
					found = true
					break
				}
				if !reflect.DeepEqual(goCalls, calls) {
					t.Errorf("Errorf(%s): Go calls %v, the model %v", describe(format, a),
						goCalls, calls)
				}
				if !matches(merr.Error(), gerr.Error()) {
					t.Errorf("Errorf(%s).Error() = %q, the model's %q", describe(format, a),
						gerr.Error(), merr.Error())
				}
				mk, mw := errKind(merr)
				if mk == gk && reflect.DeepEqual(mw, gw) {
					found = true
				}
			}
			if !found {
				t.Errorf("Errorf(%s): Go's error is of kind %d wrapping %v, no choice of the "+
					"model's is", describe(format, a), gk, gw)
			}
		}
	}
}
