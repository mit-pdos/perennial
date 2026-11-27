// Package fmt_test checks, against Go's fmt, the behaviour of fmt.Sprintf that the model printer's
// doPrintf (goose/model/overlay/fmt/printmodel.go: formatArg, strArg) relies on; the models of
// errorf, Fprintf and Printf format with it (Sprintf itself is the real fmt's, translated). Only
// tests: nothing here is translated.
package fmt_test

import (
	"fmt"
	"testing"
)

// Strings with the bytes that could make %v differ from %s: none, '%' (formatting directives in
// the operand are not interpreted), invalid UTF-8 (copied, not replaced by U+FFFD), NUL, multi-byte
// UTF-8, and digits.
var samples = []string{
	"", "a", "abc-123", "%", "%v", "%s", "%%", "%!(EXTRA)", "%!v(MISSING)",
	"\xff", "\xff\xfe", "a\x80b", "\xed\xa0\x80", "x\x00y", "\x00", "日本", "12345678", " lead",
}

// A named string type without methods (as k8s.io/apimachinery/pkg/types.UID).
type plainName string

// A named string type with a String method: Go calls it.
type stringerName string

func (s stringerName) String() string { return "S(" + string(s) + ")" }

// A named string type with an Error method: Go calls it.
type errorName string

func (s errorName) Error() string { return "E(" + string(s) + ")" }

// A named string type whose String has another signature: not a fmt.Stringer, so Go formats the
// string.
type oddStringName string

func (s oddStringName) String() int { return 0 }

// A named string type whose String has a pointer receiver: a value of it is not a fmt.Stringer,
// so Go formats the string.
type ptrStringName string

func (s *ptrStringName) String() string { return "P" }

// %v of a string is the string itself, byte for byte, as %s gives it; alone, inside other text,
// and next to other directives. (The model formats %v of an interface holding a `string` so.)
func TestSprintfVString(t *testing.T) {
	for _, s := range samples {
		if got := fmt.Sprintf("%v", s); got != s {
			t.Errorf("Sprintf(%%v, %q) = %q, want the string", s, got)
		}
		if gv, gs := fmt.Sprintf("%v", s), fmt.Sprintf("%s", s); gv != gs {
			t.Errorf("%q: %%v gave %q, %%s gave %q", s, gv, gs)
		}
		if got, want := fmt.Sprintf("p:%v/q:%v|%d", s, s+"z", 7), "p:"+s+"/q:"+s+"z|7"; got != want {
			t.Errorf("Sprintf(p:%%v/q:%%v|%%d, %q, ...) = %q, want %q", s, got, want)
		}
		var x any = s
		if got := fmt.Sprintf("%v", x); got != s {
			t.Errorf("Sprintf(%%v, any(%q)) = %q, want the string", s, got)
		}
	}
}

// %v and %s of a named string type without formatting methods are its string, byte for byte, as
// the model formats them (strArg); a type with a String or Error method is formatted by it, and
// the model does not format it (strArg's ok is false: the rest of the output is arbitrary).
func TestSprintfVNamedString(t *testing.T) {
	for _, s := range samples {
		for _, x := range []any{plainName(s), oddStringName(s), ptrStringName(s)} {
			for _, verb := range []string{"%v", "%s"} {
				if got := fmt.Sprintf(verb, x); got != s {
					t.Errorf("Sprintf(%s, %T(%q)) = %q, want the string", verb, x, s, got)
				}
			}
			if got, want := fmt.Sprintf("p: %v, q: %v", x, x), "p: "+s+", q: "+s; got != want {
				t.Errorf("Sprintf(p: %%v, q: %%v, %T(%q) twice) = %q, want %q", x, s, got, want)
			}
		}
		if got, want := fmt.Sprintf("%v", stringerName(s)), "S("+s+")"; got != want {
			t.Errorf("Sprintf(%%v, stringerName(%q)) = %q, want %q", s, got, want)
		}
		if got, want := fmt.Sprintf("%s", errorName(s)), "E("+s+")"; got != want {
			t.Errorf("Sprintf(%%s, errorName(%q)) = %q, want %q", s, got, want)
		}
	}
}

// The model's strArg agrees with Go: where it returns ok, Go's %v and %s give exactly its
// string; it returns ok for every string and method-less named string type, and not for a type
// with a formatting method or a non-string kind.
func TestStrArgModel(t *testing.T) {
	for _, s := range samples {
		args := []any{s, plainName(s), oddStringName(s), ptrStringName(s), stringerName(s),
			errorName(s), []byte(s), len(s), nil}
		wantOk := []bool{true, true, true, true, false, false, false, false, false}
		for k, x := range args {
			got, ok := strArg(x)
			if ok != wantOk[k] {
				t.Errorf("strArg(%T(%q)): ok = %v, want %v", x, s, ok, wantOk[k])
			}
			if !ok {
				continue
			}
			for _, verb := range []string{"%v", "%s"} {
				if g := fmt.Sprintf(verb, x); g != got {
					t.Errorf("Sprintf(%s, %T(%q)) = %q, model %q", verb, x, s, g, got)
				}
			}
		}
	}
}
