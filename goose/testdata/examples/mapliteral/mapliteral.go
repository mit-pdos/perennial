package example

func f() uint64 {
	return 1
}

type Nested struct {
	X uint64
}

func mapliteral() map[uint64]uint64 {
	return map[uint64]uint64{1: 2}
}

func nestedMapLiteral() map[uint64]Nested {
	return map[uint64]Nested{
		1: {X: f()},
	}
}
