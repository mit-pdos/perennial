package unittest

func useRuneOps(r rune) rune {
	r++
	r = 'a'
	r = 47
	x := int32(rune('b'))
	r = rune(x)
	return r
}
