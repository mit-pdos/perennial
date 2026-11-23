package strings

import "testing"

// ByteSliceToString converts as string(a) does, on every byte value.
func TestByteSliceToString(t *testing.T) {
	a := make([]byte, 0, 512)
	for i := 0; i < 256; i++ {
		a = append(a, byte(i), byte(255-i))
	}
	if ByteSliceToString(a) != string(a) {
		t.Fatal("ByteSliceToString(a) != string(a)")
	}
	if ByteSliceToString(nil) != "" {
		t.Fatal("ByteSliceToString(nil) != \"\"")
	}
}
