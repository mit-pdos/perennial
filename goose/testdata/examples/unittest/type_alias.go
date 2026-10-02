package unittest

type my_u64 = uint64

type Timestamp uint64

type UseTypeAbbrev my_u64

type UseNamedType Timestamp

func convertToAlias() Timestamp {
	x := uint64(2)
	return Timestamp(x)
}
