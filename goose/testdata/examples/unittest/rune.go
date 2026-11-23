package unittest

func useRuneOps(r rune) rune {
	r++
	r = 'a'
	r = 47
	x := int32(rune('b'))
	r = rune(x)
	return r
}

// a struct with a rune field (rune is int32's alias; go/types names it "rune")
type runeStruct struct {
	r rune
	n int32
}

func useRuneStruct(s runeStruct) rune {
	return s.r + rune(s.n)
}
