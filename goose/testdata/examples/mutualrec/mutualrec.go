package mutualrec

func A() { // ERROR cycle in dependencies
	B()
}

func B() {
	A()
}
