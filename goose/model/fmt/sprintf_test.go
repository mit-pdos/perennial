// Package fmt_test checks, against Go's fmt, the behaviour of fmt.Sprintf that the trusted model
// of Sprintf in Perennial/TrustedCode/fmt.lean (formatArg) relies on. Only tests: nothing here is
// translated.
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

// What the model leaves arbitrary: Go formats a named string type without formatting methods as
// its string too (for %v and %s), and calls the String method of one that has it. The model
// over-approximates both (the rest of the output is arbitrary), which this test documents.
func TestSprintfVNamedString(t *testing.T) {
	for _, s := range samples {
		if got := fmt.Sprintf("%v", plainName(s)); got != s {
			t.Errorf("Sprintf(%%v, plainName(%q)) = %q, want the string", s, got)
		}
		if got := fmt.Sprintf("%s", plainName(s)); got != s {
			t.Errorf("Sprintf(%%s, plainName(%q)) = %q, want the string", s, got)
		}
		if got, want := fmt.Sprintf("%v", stringerName(s)), "S("+s+")"; got != want {
			t.Errorf("Sprintf(%%v, stringerName(%q)) = %q, want %q", s, got, want)
		}
	}
}
