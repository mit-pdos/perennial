package fmt_test

// The model of fmt.Sprintf, fmt.Printf and fmt.Errorf (Perennial/TrustedCode/fmt.lean), as the Go
// its docstrings quote, for the differential tests of model_diff_test.go. Only tests: nothing here
// is translated. arbitrary, arbitraryString, underlyingAs and notModelled stand for the model's
// primitives (ArbitraryInt, an arbitrary string, TypeAssertUnderlying2, the stuck points).

import (
	"errors"
	"fmt"
	"reflect"
)

type State = fmt.State

// arbitraryMark stands for an arbitrary string in the model's output.
const arbitraryMark = "\x00<arbitrary>\x00"

func arbitraryString() string { return arbitraryMark }

// arbitraryChoice is what arbitrary() returns (the tests run each choice).
var arbitraryChoice uint64

func arbitrary() uint64 { return arbitraryChoice }

type notModelledPanic struct{}

func notModelled() { panic(notModelledPanic{}) }

// underlyingAs[T](x): reflect.ValueOf(x) read at T's kind, if x's dynamic type has T's underlying
// type (TypeAssertUnderlying2 T).
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

// kindIs[T](x): whether x's dynamic type has T's underlying type (the second result of
// TypeAssertUnderlying2 T).
func kindIs[T any](x any) bool {
	_, ok := underlyingAs[T](x)
	return ok
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


func intVerb(format string, i int) (byte, int, int, bool) {
	if i+1 < len(format) && (format[i+1] == 'd' || format[i+1] == 'v') {
		return 'd', 0, i + 2, true
	}
	if i+1 < len(format) && format[i+1] == '0' {
		j := i + 2
		var width int
		for j < len(format) && '0' <= format[j] && format[j] <= '9' && width <= 1000000 {
			width = width*10 + int(format[j]-'0')
			j++
		}
		if j > i+2 && j < len(format) && (format[j] == 'd' || format[j] == 'x') && width <= 1000000 {
			return format[j], width, j + 1, true
		}
	}
	return 0, 0, 0, false
}

func intArg(x any) (bool, uint64, bool) {
	var n int64
	if v, ok := x.(int); ok {
		n = int64(v)
	} else if v, ok := x.(int64); ok {
		n = v
	} else if v, ok := x.(int32); ok {
		n = int64(v)
	} else if v, ok := x.(int16); ok {
		n = int64(v)
	} else if v, ok := x.(int8); ok {
		n = int64(v)
	} else if v, ok := x.(uint); ok {
		return false, uint64(v), true
	} else if v, ok := x.(uint64); ok {
		return false, v, true
	} else if v, ok := x.(uint32); ok {
		return false, uint64(v), true
	} else if v, ok := x.(uint16); ok {
		return false, uint64(v), true
	} else if v, ok := x.(uint8); ok {
		return false, uint64(v), true
	} else {
		return false, 0, false
	}
	if n < 0 {
		return true, uint64(-n), true
	}
	return false, uint64(n), true
}

func namedIntArg(x any) (bool, uint64, bool) {
	if _, ok := x.(interface{ Format(State, rune) }); ok {
		return false, 0, false
	}
	if _, ok := x.(interface{ String() string }); ok {
		return false, 0, false
	}
	if _, ok := x.(error); ok {
		return false, 0, false
	}
	var n int64
	if v, ok := underlyingAs[int](x); ok {
		n = int64(v)
	} else if v, ok := underlyingAs[int64](x); ok {
		n = v
	} else if v, ok := underlyingAs[int32](x); ok {
		n = int64(v)
	} else if v, ok := underlyingAs[int16](x); ok {
		n = int64(v)
	} else if v, ok := underlyingAs[int8](x); ok {
		n = int64(v)
	} else if v, ok := underlyingAs[uint](x); ok {
		return false, uint64(v), true
	} else if v, ok := underlyingAs[uint64](x); ok {
		return false, v, true
	} else if v, ok := underlyingAs[uint32](x); ok {
		return false, uint64(v), true
	} else if v, ok := underlyingAs[uint16](x); ok {
		return false, uint64(v), true
	} else if v, ok := underlyingAs[uint8](x); ok {
		return false, uint64(v), true
	} else {
		return false, 0, false
	}
	if n < 0 {
		return true, uint64(-n), true
	}
	return false, uint64(n), true
}

func anyIntArg(x any) (bool, uint64, bool) {
	neg, mag, ok := intArg(x)
	if ok {
		return neg, mag, true
	}
	return namedIntArg(x)
}

func formatInt(neg bool, mag uint64, width int) string {
	var digits string
	for {
		digits = string([]byte{byte(mag%10) + '0'}) + digits
		mag = mag / 10
		if mag == 0 {
			break
		}
	}
	if neg {
		width--
	}
	for len(digits) < width {
		digits = "0" + digits
	}
	if neg {
		return "-" + digits
	}
	return digits
}

func formatHex(neg bool, mag uint64, width int) string {
	var digits string
	for {
		d := byte(mag % 16)
		if d < 10 {
			d = '0' + d
		} else {
			d = 'a' + (d - 10)
		}
		digits = string([]byte{d}) + digits
		mag = mag / 16
		if mag == 0 {
			break
		}
	}
	if neg {
		width--
	}
	for len(digits) < width {
		digits = "0" + digits
	}
	if neg {
		return "-" + digits
	}
	return digits
}

func modelStrArg(x any) (string, bool) {
	if _, ok := x.(interface{ Format(State, rune) }); ok {
		return "", false
	}
	if _, ok := x.(interface{ String() string }); ok {
		return "", false
	}
	if _, ok := x.(error); ok {
		return "", false
	}
	return underlyingAs[string](x)
}

func formatArg(format string, i int, x any) (string, int, bool) {
	if i+1 < len(format) && format[i+1] == 's' {
		s, ok := modelStrArg(x)
		return s, i + 2, ok
	}
	if i+1 < len(format) && format[i+1] == 'v' {
		if s, ok := modelStrArg(x); ok {
			return s, i + 2, true
		}
	}
	if i+1 < len(format) && format[i+1] == 'x' {
		neg, mag, ok := anyIntArg(x)
		if !ok {
			return "", 0, false
		}
		return formatHex(neg, mag, 0), i + 2, true
	}
	verb, width, next, ok := intVerb(format, i)
	if !ok {
		return "", 0, false
	}
	neg, mag, ok2 := anyIntArg(x)
	if !ok2 {
		return "", 0, false
	}
	if verb == 'x' {
		return formatHex(neg, mag, width), next, true
	}
	return formatInt(neg, mag, width), next, true
}


// The new parts of the model of fmt (Perennial/TrustedCode/fmt.lean). In the scratch package these
// sit next to the old helpers (oldmodel.go), with stubs for arbitrary, arbitraryString,
// underlyingAs and notModelled.

// isBasic: whether x's dynamic type is one of the predeclared types that printArg formats by its
// type switch, without handleMethods (bool, the integer types, uintptr, float32, float64, string;
// not complex64, complex128 or []byte, which the model does not follow, nor reflect.Value, which
// printArg unwraps: visitArg is stuck on a Stringer with a CanInterface() bool method, as it has).
func isBasic(x any) bool {
	switch x.(type) {
	case bool, int, int8, int16, int32, int64, uint, uint8, uint16, uint32, uint64, uintptr,
		float32, float64, string:
		return true
	}
	return false
}

// isIntKind: whether x's dynamic type has an integer kind (one of Go's ten integer types as its
// underlying type; not uintptr).
func isIntKind(x any) bool {
	return kindIs[int](x) || kindIs[int64](x) || kindIs[int32](x) || kindIs[int16](x) ||
		kindIs[int8](x) || kindIs[uint](x) || kindIs[uint64](x) || kindIs[uint32](x) ||
		kindIs[uint16](x) || kindIs[uint8](x)
}

// isStrKind: whether x's dynamic type has kind String.
func isStrKind(x any) bool {
	return kindIs[string](x)
}

// hasFmtMethod: whether x implements one of the interfaces handleMethods consults (Formatter,
// GoStringer, error, Stringer).
func hasFmtMethod(x any) bool {
	if _, ok := x.(interface{ Format(State, rune) }); ok {
		return true
	}
	if _, ok := x.(interface{ GoString() string }); ok {
		return true
	}
	if _, ok := x.(error); ok {
		return true
	}
	if _, ok := x.(interface{ String() string }); ok {
		return true
	}
	return false
}

// inert: whether Go formats x, under any directive, without calling any of its methods or reading
// memory: nil, a predeclared basic type, or a type of integer or string kind that implements none
// of handleMethods' interfaces.
func inert(x any) bool {
	if x == nil {
		return true
	}
	if isBasic(x) {
		return true
	}
	if hasFmtMethod(x) {
		return false
	}
	if isStrKind(x) {
		return true
	}
	return isIntKind(x)
}

// allInert: whether every argument is inert.
func allInert(a []any) bool {
	for _, x := range a {
		if !inert(x) {
			return false
		}
	}
	return true
}

// parseDirective reads the directive whose bytes start at format[i], after its '%', as doPrintf
// does: flags among '#', '0', '+', '-', ' '; a decimal width; '.' and a decimal precision (only if
// a byte follows the '.'); the verb. It returns the verb (as an int; -1 if the format ends first,
// Go's %!(NOVERB)), whether the directive is %#v or %#w (Go's sharpV), and the index after it.
// ok is false where the model does not follow Go: a '*' width or precision, an argument index
// '[', or a width or precision of more than 7 digits.
func parseDirective(format string, i int) (int, bool, int, bool) {
	var sharp bool
	var phase int // 0: flags, 1: width, 2: precision
	var n int     // digits read of the width or precision
	for i < len(format) {
		c := format[i]
		if phase == 0 && c == '#' {
			sharp = true
			i++
			continue
		}
		if phase == 0 && (c == '+' || c == '-' || c == '0' || c == ' ') {
			i++
			continue
		}
		if '0' <= c && c <= '9' {
			if phase == 0 {
				phase = 1
				n = 1
				i++
				continue
			}
			if n >= 7 {
				return 0, false, 0, false
			}
			n++
			i++
			continue
		}
		if phase < 2 && c == '.' && i+1 < len(format) {
			phase = 2
			n = 0
			i++
			continue
		}
		if c == '*' || c == '[' {
			return 0, false, 0, false
		}
		return int(c), sharp && (c == 'v' || c == 'w'), i + 1, true
	}
	return -1, false, i, true
}

// visitKind: printValue of x by its kind, without its methods: the model follows it for the
// integer and string kinds, which read no memory, and is not defined for the others.
func visitKind(x any) {
	if isStrKind(x) {
		return
	}
	if isIntKind(x) {
		return
	}
	notModelled()
}

// visitArg calls the methods of x that Go's printArg calls under the directive (verb, sharpV),
// and nothing else; the output is not modelled.
func visitArg(x any, verb byte, sharpV bool, wrapErrs bool) {
	if x == nil {
		return
	}
	if verb == 'T' || verb == 'p' {
		return
	}
	if isBasic(x) {
		return
	}
	if verb == 'w' {
		if _, ok := x.(error); !ok || !wrapErrs {
			visitKind(x)
			return
		}
		verb = 'v'
	}
	if _, ok := x.(interface{ Format(State, rune) }); ok {
		notModelled()
	}
	if sharpV {
		if _, ok := x.(interface{ GoString() string }); ok {
			notModelled()
		}
	} else if verb == 'v' || verb == 's' || verb == 'x' || verb == 'X' || verb == 'q' {
		if e, ok := x.(error); ok {
			e.Error()
			return
		}
		if s, ok := x.(interface{ String() string }); ok {
			if _, ok := x.(interface{ CanInterface() bool }); ok {
				notModelled() // a reflect.Value, which printArg unwraps
			}
			s.String()
			return
		}
	}
	visitKind(x)
}

// visitRest goes through the directives of format from index i, the arguments from argNum,
// calling what Go calls of each argument (visitArg), and then of each argument left over (Go's
// %!(EXTRA ...), under %v). It returns the indices of the arguments of the %w directives, and
// whether it gave up at a directive the model does not follow, every argument being inert.
func visitRest(format string, i int, a []any, argNum int, wrapErrs bool) ([]int, bool) {
	var wrapped []int
	for i < len(format) {
		if format[i] != '%' {
			i++
			continue
		}
		verb, sharpV, next, ok := parseDirective(format, i+1)
		if !ok {
			if allInert(a) {
				return wrapped, true
			}
			notModelled()
		}
		i = next
		if verb < 0 || verb == '%' {
			continue
		}
		if argNum >= len(a) {
			continue
		}
		if verb == 'w' {
			wrapped = append(wrapped, argNum)
		}
		visitArg(a[argNum], byte(verb), sharpV, wrapErrs)
		argNum++
	}
	for argNum < len(a) {
		visitArg(a[argNum], 'v', false, wrapErrs)
		argNum++
	}
	return wrapped, false
}

// doPrintf: the formatted string, the indices of the arguments of the %w directives, and whether
// those are unknown (visitRest gave up). It formats as the previous model of Sprintf did, up to
// the first directive it does not format or whose argument is not inert; from there the output is
// arbitrary, and visitRest makes the calls Go makes.
func doPrintf(format string, a []any, wrapErrs bool) (string, []int, bool) {
	var out string
	var argNum int
	var i int
	for i < len(format) {
		if format[i] != '%' {
			out += string([]byte{format[i]})
			i++
			continue
		}
		if i+1 < len(format) && format[i+1] == '%' {
			out += "%"
			i += 2
			continue
		}
		if argNum < len(a) && inert(a[argNum]) {
			s, next, ok := formatArg(format, i, a[argNum])
			if ok {
				out += s
				argNum++
				i = next
				continue
			}
		}
		wrapped, unknown := visitRest(format, i, a, argNum, wrapErrs)
		return out + arbitraryString(), wrapped, unknown
	}
	if argNum < len(a) {
		wrapped, unknown := visitRest(format, i, a, argNum, wrapErrs)
		return out + arbitraryString(), wrapped, unknown
	}
	return out, nil, false
}

func modelSprintf(format string, a ...any) string {
	s, _, _ := doPrintf(format, a, false)
	return s
}

func modelPrintf(format string, a ...any) (int, error) {
	doPrintf(format, a, false)
	n := int(arbitrary())
	if arbitrary() == 0 {
		return n, nil
	}
	return n, errors.New(arbitraryString())
}

func modelErrorf(format string, a ...any) error {
	s, wrapped, unknown := doPrintf(format, a, true)
	if unknown {
		n := arbitrary()
		if n == 0 {
			return errors.New(s)
		}
		if n == 1 {
			return &wrapError{msg: s}
		}
		return &wrapErrors{msg: s}
	}
	if len(wrapped) == 0 {
		return errors.New(s)
	}
	if len(wrapped) == 1 {
		w := &wrapError{msg: s}
		w.err, _ = a[wrapped[0]].(error)
		return w
	}
	var errs []error
	for _, argNum := range wrapped {
		if e, ok := a[argNum].(error); ok {
			errs = append(errs, e)
		}
	}
	return &wrapErrors{s, errs}
}
