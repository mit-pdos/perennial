package shift_typeparam

// whether a count of a type-parameter type is signed (and so may be negative,
// which panics) depends on the instantiation.

func Shl[T ~int8 | ~uint](x int, y T) int {
	return x << y // ERROR shift count of type T (not a basic integer type)
}
