package strings

func StringToByteSlice(s string) (a []byte) {
	// FIXME: support and then use `range len(s)`
	for i := 0; i < len(s); i++ {
		a = append(a, s[i])
	}
	return
}

func ByteSliceToString(a []byte) (s string) {
	for _, c := range a {
		s = s + string(c)
	}
	return
}
