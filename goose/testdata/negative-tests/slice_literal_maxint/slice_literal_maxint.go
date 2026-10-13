package slice_literal_maxint

// A slice literal with index math.MaxInt would have length 2^63 (gc miscompiles it).

func maxIntLiteral() []byte {
	return []byte{9223372036854775807: 1} // ERROR composite literal index math.MaxInt
}
