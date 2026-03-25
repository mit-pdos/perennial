package unittest

func LocalVars() int {
	var (
		a int
		b string
	)
	b += "hello"
	return a
}

func LocalConsts() (x int) {
	const (
		c = 10
		d = c + 5
	)
	const e = 1 << 3
	x += c
	x -= d
	return x
}
