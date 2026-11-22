package strings

import (
	"strings"
	"testing"
)

// TestBuilderStringAliases is the evidence for the model of (*strings.Builder).String
// (Perennial/TrustedCode/strings.lean, Builder.String.impl): gc's String shares the
// Builder's buffer, so a Builder restored from a copy by value (copyCheck passes:
// its addr is its own address again) overwrites the bytes of a string returned
// earlier. The model returns a copy and leaves a reader on those bytes, so that the
// overwrite is stuck there, never different.
func TestBuilderStringAliases(t *testing.T) {
	var b strings.Builder
	b.Grow(8)
	b.WriteString("a")
	saved := b
	b.WriteString("b")
	s := b.String()
	if s != "ab" {
		t.Fatalf("String() = %q, want \"ab\"", s)
	}
	b = saved
	b.WriteString("c")
	if s != "ac" {
		t.Fatalf("after the overwrite, s = %q; gc's String no longer aliases the buffer, and the model's read-lock is no longer needed", s)
	}
}

// TestBuilderCopyPanics: a write through a copy of a non-zero Builder panics
// (copyCheck), which the translated copyCheck keeps.
func TestBuilderCopyPanics(t *testing.T) {
	var b strings.Builder
	b.WriteString("a")
	c := b
	defer func() {
		if recover() == nil {
			t.Fatal("WriteString on a copy did not panic")
		}
	}()
	c.WriteString("b")
}
