package unittest

func BasicNamedReturn() (x string) {
	return "ok"
}

func NamedReturn() (x string) {
	x = x + "foo"
	return
}

func BasicNamedReturnMany() (x string, y string) {
	return "ok", "blah"
}

func NamedReturnMany() (x string, y string) {
	x = "returned"
	y = "ok"
	return
}

func NamedReturnOverride() (x string, y string) {
	for {
		x := "unused"
		x += "stillUnused"
		y = "ok"
		break
	}
	return
}

func VoidButEndsWithReturn() {
	// translation should not produce the value from this function call since the
	// outer function is void
	BasicNamedReturn()
}

func VoidImplicitReturnInBranch(b bool) {
	if b {
		return
	} else {
		BasicNamedReturn()
	}
}
