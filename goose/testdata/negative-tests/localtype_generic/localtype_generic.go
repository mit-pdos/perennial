package localtype_generic

// A local type of a generic function is a different type for each
// instantiation (L[int] and L[string]), but goose would translate it as one
// package-level type.

func f[T any](x any) any {
	type L struct{ X int } // ERROR local type in a generic function
	if x != nil {
		return x.(L)
	}
	return L{}
}
