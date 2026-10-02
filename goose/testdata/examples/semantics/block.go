package semantics

func testExplicitBlockStmt() bool {
	x := 10
	{
		x := 11
		x += 1
	}
	return (x == 10)
}
