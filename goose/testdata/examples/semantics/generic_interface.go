package semantics

// A value of a type parameter is converted to an interface wherever Go assigns
// it to one: an argument, a result, an assignment, a composite literal element.

func genericAnyArg(x any) any {
	return x
}

func genericToAny[T any](x T) any {
	var y any
	y = x
	if genericAnyArg(x) != y {
		return nil
	}
	return x
}

func genericSliceOfAny[T any](x T) []any {
	return []any{x}
}

func genericFuncToAny[T any](f func() T) func() any {
	return func() any { return f() }
}

func testGenericToInterface() bool {
	var p *int = new(int)
	var e any = p
	var i any = 3
	return genericToAny(p) == e && genericToAny(3) == i &&
		genericToAny(e) == e && genericToAny[any](nil) == nil
}

func testGenericToInterfaceLiteralClosure() bool {
	var e any = 3
	return genericSliceOfAny(3)[0] == e && genericFuncToAny(func() int { return 3 })() == e
}
