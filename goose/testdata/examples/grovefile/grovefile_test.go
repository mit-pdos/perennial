package grovefile

import (
	"os"
	"testing"
)

// TestRun runs Run against the real grove_ffi, which keeps files under
// durable/ (and temporary files under tmp/) in the working directory.
func TestRun(t *testing.T) {
	t.Chdir(t.TempDir())
	Run()
	got, err := os.ReadFile("durable/f")
	if err != nil {
		t.Fatal(err)
	}
	if string(got) != "hello" {
		t.Fatalf("durable/f holds %q, want %q", got, "hello")
	}
}
