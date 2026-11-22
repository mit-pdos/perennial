package labels

import "testing"

// Each test* function of package labels returns true in Go.
func TestLabeledContinue(t *testing.T) {
	if !testLabeledContinue() {
		t.Fatal("testLabeledContinue returned false")
	}
}

func TestLabeledBreak(t *testing.T) {
	if !testLabeledBreak() {
		t.Fatal("testLabeledBreak returned false")
	}
}

func TestBreakLoopFromSwitch(t *testing.T) {
	if !testBreakLoopFromSwitch() {
		t.Fatal("testBreakLoopFromSwitch returned false")
	}
}

func TestContinueNestedSwitch(t *testing.T) {
	if !testContinueNestedSwitch() {
		t.Fatal("testContinueNestedSwitch returned false")
	}
}

func TestLabeledSwitch(t *testing.T) {
	if !testLabeledSwitch() {
		t.Fatal("testLabeledSwitch returned false")
	}
}

func TestLabeledSelect(t *testing.T) {
	if !testLabeledSelect() {
		t.Fatal("testLabeledSelect returned false")
	}
}

func TestRangeSliceLabeled(t *testing.T) {
	if !testRangeSliceLabeled() {
		t.Fatal("testRangeSliceLabeled returned false")
	}
}

func TestRangeMapLabeled(t *testing.T) {
	if !testRangeMapLabeled() {
		t.Fatal("testRangeMapLabeled returned false")
	}
}

func TestRangeMapBreakLabeled(t *testing.T) {
	if !testRangeMapBreakLabeled() {
		t.Fatal("testRangeMapBreakLabeled returned false")
	}
}

func TestRangeIntLabeled(t *testing.T) {
	if !testRangeIntLabeled() {
		t.Fatal("testRangeIntLabeled returned false")
	}
}

func TestRangeFuncLabeled(t *testing.T) {
	if !testRangeFuncLabeled() {
		t.Fatal("testRangeFuncLabeled returned false")
	}
}

func TestBreakThroughRangeFunc(t *testing.T) {
	if !testBreakThroughRangeFunc() {
		t.Fatal("testBreakThroughRangeFunc returned false")
	}
}

func TestReturnInLabeledLoop(t *testing.T) {
	if !testReturnInLabeledLoop() {
		t.Fatal("testReturnInLabeledLoop returned false")
	}
}

func TestClosureAcrossContinue(t *testing.T) {
	if !testClosureAcrossContinue() {
		t.Fatal("testClosureAcrossContinue returned false")
	}
}

func TestSameLabelNested(t *testing.T) {
	if !testSameLabelNested() {
		t.Fatal("testSameLabelNested returned false")
	}
}

func TestCountPairs(t *testing.T) {
	if !testCountPairs() {
		t.Fatal("testCountPairs returned false")
	}
}

func TestMiniPrintf(t *testing.T) {
	if !testMiniPrintf() {
		t.Fatal("testMiniPrintf returned false")
	}
}
