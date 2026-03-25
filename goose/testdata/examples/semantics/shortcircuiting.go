package semantics

// helpers
type BoolTest struct {
	t  bool
	f  bool
	tc uint64
	fc uint64
}

func CheckTrue(b *BoolTest) bool {
	b.tc += 1
	return b.t
}

func CheckFalse(b *BoolTest) bool {
	b.fc += 1
	return b.f
}

// tests
func testShortcircuitAndTF() bool {
	b := &BoolTest{t: true, f: false, tc: 0, fc: 0}

	if CheckTrue(b) && CheckFalse(b) {
		return false
	}
	return b.tc == 1 && b.fc == 1
}

func testShortcircuitAndFT() bool {
	b := &BoolTest{t: true, f: false, tc: 0, fc: 0}

	if CheckFalse(b) && CheckTrue(b) {
		return false
	}
	return b.tc == 0 && b.fc == 1
}

func testShortcircuitOrTF() bool {
	b := &BoolTest{t: true, f: false, tc: 0, fc: 0}
	if CheckTrue(b) || CheckFalse(b) {
		return b.tc == 1 && b.fc == 0
	}
	return false
}

func testShortcircuitOrFT() bool {
	b := &BoolTest{t: true, f: false, tc: 0, fc: 0}
	if CheckFalse(b) || CheckTrue(b) {
		return b.tc == 1 && b.fc == 1
	}
	return false
}
