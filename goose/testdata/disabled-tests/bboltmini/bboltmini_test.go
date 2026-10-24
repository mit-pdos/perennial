package bboltmini

import "testing"

// The targets hold in Go; the proofs are to show they hold in the model.
func TestTargets(t *testing.T) {
	for name, f := range map[string]func() bool{
		"testEndianness":        testEndianness,
		"testLeafRoundTrip":     testLeafRoundTrip,
		"testBranchRoundTrip":   testBranchRoundTrip,
		"testPageAtOffset":      testPageAtOffset,
		"testAliasing":          testAliasing,
		"testSearch":            testSearch,
		"testMetaChecksum":      testMetaChecksum,
		"testFreelistRoundTrip": testFreelistRoundTrip,
		"testFreelistOverflow":  testFreelistOverflow,
		"testInlineBucket":      testInlineBucket,
		"testStatsConcurrent":   testStatsConcurrent,

		"testDisjointStructCopy":      testDisjointStructCopy,
		"testTagsClearedByByteStores": testTagsClearedByByteStores,
		"testOverlappingLoads":        testOverlappingLoads,
	} {
		if !f() {
			t.Errorf("%s returned false", name)
		}
	}
}
