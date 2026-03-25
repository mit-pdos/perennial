package generics

func UnderlyingSlice[T ~[]int](s T) int {
	return len(s)
}

// Clone copies a generic slice.
//
// Slightly simplified from [slices.Clone].
func Clone[S ~[]E, E any](s S) S {
	return append(S{}, s...)
}
