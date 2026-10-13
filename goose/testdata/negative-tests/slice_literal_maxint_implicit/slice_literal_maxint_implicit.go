package slice_literal_maxint_implicit

// The element after index math.MaxInt-1 has index math.MaxInt: the literal would have
// length 2^63 (gc miscompiles it).

func implicit() []struct{} {
	return []struct{}{9223372036854775806: {}, {}} // ERROR composite literal index math.MaxInt
}
