package unittest

type my_u64 = uint64

type Timestamp uint64

type UseTypeAbbrev my_u64

type UseNamedType Timestamp

func convertToAlias() Timestamp {
	x := uint64(2)
	return Timestamp(x)
}

type aliasedStruct struct {
	x uint64
}

type structAlias = aliasedStruct

func readAliasField(a structAlias) uint64 {
	return a.x
}

func readAliasFieldPtr(p *structAlias) uint64 {
	return p.x
}
