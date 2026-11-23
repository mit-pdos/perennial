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

// A map type parameter is ranged over, indexed and assigned to as its core
// type (from [maps.Equal] and [maps.Copy]).
func MapEqualCopy[M ~map[K]V, K, V comparable](m1, m2 M) bool {
	for k, v1 := range m1 {
		if v2, ok := m2[k]; !ok || v1 != v2 {
			return false
		}
		v := m1[k]
		m2[k] = v
	}
	return true
}
