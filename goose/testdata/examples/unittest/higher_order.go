package unittest

func TakesFunctionType(f func()) {
	f()
}

func FuncVar() {
	var f func()
	_ = f
}
