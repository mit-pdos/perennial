package unittest

func maybeConvert[A interface{ int8 | uint8 }](a A) uint32 {
	return uint32(a)
}

func maybeConvertToInterface[A any](a A) any {
	return a
}

func maybeConvertToString[A interface{ string | []byte }](a A) string {
	return string(a)
}

func maybeConvertFromString[A interface{ string | []byte }](a A) []byte {
	return []byte(a)
}

func assert(b bool, s string) {
	if !b {
		panic(s)
	}
}

func nilConvert[A interface{ *int | []int }]() []A {
	return []A{nil}
}

func genericConversions() {
	var x int8 = -1
	assert(maybeConvert(x) == 4294967295 && maybeConvert(uint8(x)) == 255, "")
	assert(maybeConvertToString(maybeConvertFromString("ok")) == "ok", "")
	assert(maybeConvertToInterface("ok") == "ok", "")
	assert(maybeConvertToInterface(maybeConvertToInterface("ok")).(string) == "ok", "")
	assert(&(nilConvert[[]int]()[0][0]) == nilConvert[*int]()[0], "")
}
