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

//go:noinline
func growStack(n int) int {
	var pad [64]byte
	if n == 0 {
		return int(pad[0])
	}
	return growStack(n-1) + int(pad[n%64])
}

var staleSaved strings.Builder

// TestBuilderStaleCopyPanics is the evidence for the model of (*strings.Builder).copyCheck
// (Perennial/TrustedCode/strings.lean, Builder.copyCheck.impl): b stays on the stack
// (copyCheck hides b.addr from escape analysis), a copy by value kept on the heap holds
// b's address, and once the stack has moved that address is stale, so storing the copy
// back over b and writing panics. The model's copyCheck leaves a reader on b.addr, so
// that the store back is stuck there; with b.addr = b alone the write would succeed.
func TestBuilderStaleCopyPanics(t *testing.T) {
	var b strings.Builder
	b.WriteString("a")
	staleSaved = b
	growStack(10000)
	b = staleSaved
	defer func() {
		if recover() == nil {
			t.Fatal("WriteString after restoring a stale copy did not panic; the model's reader on addr may no longer be needed")
		}
	}()
	b.WriteString("c")
}

// TestBuilderCopyBackNoMove: without a stack move the same restore does not panic in gc
// (the model is stuck at the store: less defined, never more).
func TestBuilderCopyBackNoMove(t *testing.T) {
	var b strings.Builder
	b.WriteString("a")
	saved := b
	b = saved
	b.WriteString("c")
	if b.String() != "ac" {
		t.Fatalf("got %q", b.String())
	}
}
