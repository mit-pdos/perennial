package stuck

import "testing"

// What Go does, to keep the comments in stuck.go honest. The probes that read
// past an allocation or depend on alignment have no fixed answer and are not
// run.
func TestGo(t *testing.T) {
	for name, c := range map[string]struct {
		f    func() bool
		want bool
	}{
		"testOriginalUnsafeAdd": {testOriginalUnsafeAdd, true},
		"testOriginalPos":       {testOriginalPos, true},
		"testPointerFromBytes":  {testPointerFromBytes, true},
		"testBytesOverPointer":  {testBytesOverPointer, true},
		"testFloatBits":         {testFloatBits, true},
		"testPaddedView":        {testPaddedView, true},
		"testFieldResidue":      {testFieldResidue, false},
		"testZeroSizeDistinct":  {testZeroSizeDistinct, false},
		"testOverlappingCopy":   {testOverlappingCopy, false},

		"testOverlappingCopyViaTemp": {testOverlappingCopyViaTemp, true},
	} {
		if got := c.f(); got != c.want {
			t.Errorf("%s = %v in Go, want %v", name, got, c.want)
		}
	}
}
