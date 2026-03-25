package unittest

func ifJoinDemo(arg1, arg2 bool) {
	arr := []int{}
	if arg1 {
		arr = append(arr, 2)
	}
	if arg2 {
		arr = append(arr, 3)
	}
}

func repeatLocalVars() {
	g := 0
	{
		a := 2
		g = a
	}
	{
		a := 3
		g = a
	}
	if g != 3 {
		panic("failure")
	}
}
