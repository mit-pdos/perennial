// TestModelAlias: the printer's buffer, which Fprintf and Fprint hand to w.Write, is observable
// outside fmt. A writer that keeps the slice aliases the buffer of the printer that fmt's pool
// (ppFree) hands out again, so a later Errorf's message, or what a String method reads or writes
// through the slice while Fprintf or Fprint prints, depends on what the printer appended to its
// buffer and when (the adversarial review of S3's fmt models, gmr-adv-fmt/demo).
//
// The test is a file of package fmt_test that etc/model-tests.sh adds to the standard library's
// fmt with go test -overlay, twice: on the real fmt, where it checks that Go gives the results
// below (the scenario reuses the pooled printer, as gc's sync.Pool does with the garbage collector
// off and one goroutine); and on fmt with its Go models (with -tags goose, the internal/gomodel of
// gomodel_driven.go), where it checks that the model gives the same results, for the choices of
// Choose and ChooseUint64 that each case drives: Go's results are among the model's.
package fmt_test

import (
	"fmt"
	"runtime/debug"
	"testing"
)

// drive makes the model's next choices those of s (alias_goose_test.go); on the real fmt, which
// chooses nothing, it does nothing.
var drive = func(s []uint64) {}

var saved []byte

// keep is a writer that keeps the slice Write receives: the printer's buffer.
type keep struct{}

func (keep) Write(b []byte) (int, error) { saved = b; return len(b), nil }

// rec is a writer that records a copy of what Write receives.
type rec struct{ got string }

func (r *rec) Write(b []byte) (int, error) { r.got = string(b); return len(b), nil }

var seen string

// peek reads the kept slice while fmt prints.
type peek struct{}

func (peek) String() string { seen = string(saved[:4]); return "" }

// poke writes into the kept slice while fmt prints.
type poke struct{}

func (poke) String() string { saved[0] = 'Z'; return "" }

// chooseStringScript is the choices that make the model's chooseString return s.
func chooseStringScript(s string) []uint64 {
	var c []uint64
	for i := 0; i < len(s); i++ {
		c = append(c, 1, uint64(s[i]))
	}
	return append(c, 0)
}

func TestModelAlias(t *testing.T) {
	defer debug.SetGCPercent(debug.SetGCPercent(-1))
	cases := []struct {
		name   string
		script []uint64
		run    func() string
		want   string
	}{
		{"Errorf's message in the kept buffer", nil, func() string {
			fmt.Fprintf(keep{}, "hello world")
			_ = fmt.Errorf("abc %d", 5)
			return string(saved)
		}, "abc 5 world"},
		{"Fprintf: a String method reads the buffer", nil, func() string {
			fmt.Fprintf(keep{}, "hello world")
			fmt.Fprintf(keep{}, "XYZW%v", peek{})
			return seen
		}, "XYZW"},
		// The model: "XYZW" appended (writeArbitrary: chooseString, then Choose false) before the
		// first operand, nothing before the second.
		{"Fprint: a String method reads the buffer", append(chooseStringScript("XYZW"), 0), func() string {
			fmt.Fprintf(keep{}, "hello world")
			fmt.Fprint(keep{}, "XYZW", peek{})
			return seen
		}, "XYZW"},
		{"Fprintf: a String method writes the buffer", nil, func() string {
			fmt.Fprintf(keep{}, "hello world")
			var r rec
			fmt.Fprintf(&r, "ab%v", poke{})
			return r.got
		}, "Zb"},
		{"Errorf: a String method writes the buffer", nil, func() string {
			fmt.Fprintf(keep{}, "hello world")
			return fmt.Errorf("ab%v", poke{}).Error()
		}, "Zb"},
	}
	for _, c := range cases {
		// The pool may (rarely) hand out another printer, if the goroutine moved to another P:
		// try a few times.
		var got string
		for try := 0; try < 5; try++ {
			drive(c.script)
			if got = c.run(); got == c.want {
				break
			}
		}
		if got != c.want {
			t.Errorf("%s: %q, want %q", c.name, got, c.want)
		}
	}
}
