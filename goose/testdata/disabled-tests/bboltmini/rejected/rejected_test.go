package rejected

import (
	"bufio"
	"errors"
	"os"
	"strings"
	"testing"

	"github.com/mit-pdos/perennial/goose"
	"github.com/mit-pdos/perennial/goose/modelcheck"
)

// What Go does, to keep the comments in rejected.go honest.
func TestGo(t *testing.T) {
	for name, c := range map[string]struct {
		f    func() bool
		want bool
	}{
		"testOverlappingCopy":       {testOverlappingCopy, false},
		"testOverlappingArrayCopy":  {testOverlappingArrayCopy, true},
		"testArrayFieldOverlapCopy": {testArrayFieldOverlapCopy, false},
		"testCopyViaPointerFields":  {testCopyViaPointerFields, false},
		"testCopyViaSliceFields":    {testCopyViaSliceFields, false},
		"testCopyViaNestedSlices":   {testCopyViaNestedSlices, false},
	} {
		if got := c.f(); got != c.want {
			t.Errorf("%s = %v in Go, want %v", name, got, c.want)
		}
	}
}

// goose's guard reports exactly the lines of rejected.go marked "// refused".
func TestRefused(t *testing.T) {
	want := make(map[int]bool)
	f, err := os.Open("rejected.go")
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	for line := 1; sc.Scan(); line++ {
		if strings.HasSuffix(sc.Text(), "// refused") {
			want[line] = true
		}
	}

	_, errs, patternErr := goose.TranslatePackages(".", ".", ".")
	if patternErr != nil {
		t.Fatal(patternErr)
	}
	got := make(map[int]bool)
	for _, e := range errs {
		var merr goose.MultipleErrors
		if !errors.As(e, &merr) {
			continue
		}
		for _, e := range merr {
			var ce *goose.ConversionError
			if errors.As(e, &ce) && strings.HasPrefix(ce.Message, modelcheck.Prefix) {
				got[ce.Position.Line] = true
				if !want[ce.Position.Line] {
					t.Errorf("rejected.go:%d: unexpected finding: %s", ce.Position.Line, ce.Message)
				}
			}
		}
	}
	for line := range want {
		if !got[line] {
			t.Errorf("rejected.go:%d: goose translates this copy", line)
		}
	}
}
