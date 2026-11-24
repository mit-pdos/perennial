package reflectcore

// The generic helpers that the primitive stubs instantiate at a dynamic
// type (TrustedCode/internal/reflectcore.lean): translated Go.

func tokOf[T any](x any) any {
	return (*T)(nil)
}

func box[T any](x any) any {
	q := new(T)
	*q = x.(T)
	return q
}

func load[T any](p any) any {
	return *p.(*T)
}

func alloc[T any](t any) any {
	return new(T)
}

func ptrTok[T any](t any) any {
	return (**T)(nil)
}

func store[T any](p any, x any) {
	if x == nil {
		var zero T
		*p.(*T) = zero
		return
	}
	*p.(*T) = x.(T)
}

func assertOk[T any](x any) bool {
	_, ok := x.(T)
	return ok
}
