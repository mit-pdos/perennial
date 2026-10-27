package localtype_generic

// a type declared in a generic function is a distinct type at each
// instantiation: F[int]'s L is not F[string]'s, so x.(L) in F[string] fails on
// a value made by F[int]

func F[P any](x any) (any, bool) {
	type L struct{} // ERROR local type L in a generic function
	_, ok := x.(L)
	return L{}, ok
}
