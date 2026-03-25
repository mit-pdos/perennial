package unittest

func stringAppend(s string) string {
	return "prefix " + s + " "
}

func stringLength(s string) uint64 {
	return uint64(len(s))
}

func x() {
	stringAppend("a" + "b")
}
