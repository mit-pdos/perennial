package semantics

// ----------------------------
// SETUP
// ----------------------------

type geometryInterface interface {
	Square() uint64
	Volume() uint64
}

func measureArea(t geometryInterface) uint64 {
	return t.Square()
}

func measureVolumePlusNM(t geometryInterface, n uint64, m uint64) uint64 {
	return t.Volume() + n + m
}

func measureVolume(t geometryInterface) uint64 {
	return t.Volume()
}

type SquareStruct struct {
	Side uint64
}

func (t SquareStruct) Square() uint64 {
	return t.Side * t.Side
}

func (t SquareStruct) Volume() uint64 {
	return t.Side * t.Side * t.Side
}

// ----------------------------
// TESTS
// ----------------------------

func testBasicInterface() bool {
	s := SquareStruct{
		Side: 2,
	}
	return measureArea(s) == 4
}

func testAssignInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	area := measureArea(s)
	return area == 9
}

func testMultipleInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	square1 := measureArea(s)
	square2 := measureArea(s)
	return square1 == square2
}

func testBinaryExprInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	square1 := measureArea(s)
	square2 := measureVolume(s)
	return square1 == measureArea(s) && square2 == measureVolume(s)
}

func testIfStmtInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	if measureArea(s) == 9 {
		return true
	}
	return false
}
