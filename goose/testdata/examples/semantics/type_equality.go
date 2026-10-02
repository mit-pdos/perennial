package semantics

func TypesEqual[T, U any]() bool {
	var t *T
	var u *U
	return any(t) == any(u)
}

func testPrimitiveTypesEqual() bool {
	return TypesEqual[int, int]() &&
		!TypesEqual[int, string]() &&
		!TypesEqual[int, uint32]() &&
		!TypesEqual[int, int64]() &&
		!TypesEqual[int, uint64]() &&
		TypesEqual[func() bool, func() bool]()
}

type DefinedStr string

type DefinedStr2 = DefinedStr

func testDefinedStrTypesEqual() bool {
	return !TypesEqual[DefinedStr, string]() &&
		TypesEqual[DefinedStr, DefinedStr2]()
}

type List[T any] struct {
	X    T
	Next *List[T]
}

func testListTypesEqual() bool {
	return TypesEqual[List[int], List[int]]() &&
		!TypesEqual[List[int], List[string]]()
}
