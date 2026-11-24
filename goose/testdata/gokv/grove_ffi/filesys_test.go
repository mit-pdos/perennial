package grove_ffi

import "testing"

// FileRead of a file that does not exist returns a non-nil empty slice.
func TestFileReadMissing(t *testing.T) {
	t.Chdir(t.TempDir())
	got := FileRead("missing")
	if got == nil || len(got) != 0 {
		t.Fatalf("FileRead(\"missing\") = %#v, want []byte{}", got)
	}
}
