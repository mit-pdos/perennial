package semantics

type blankFieldStruct struct {
	x int
	_ int
}

func testBlankFieldEq() bool {
	var evaluated = false
	setEvaluated := func() int {
		evaluated = true
		return 2
	}
	return blankFieldStruct{1, setEvaluated()} == blankFieldStruct{x: 1} && evaluated
}

func testBlankFieldMapKey() bool {
	m := make(map[blankFieldStruct]int)
	m[blankFieldStruct{1, 2}] = 3
	v, ok := m[blankFieldStruct{x: 1}]
	return ok && v == 3
}

func testBlankFieldIdentity() bool {
	return any(struct{ _ int }{}) != any(struct{ _0 int }{})
}
