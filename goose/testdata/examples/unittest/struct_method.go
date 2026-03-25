package unittest

type Point struct {
	x uint64
	y uint64
}

func (c Point) Add(z uint64) uint64 {
	return c.x + c.y + z
}

func (c Point) GetField() uint64 {
	x := c.x
	y := c.y
	return x + y
}

func UseAdd() uint64 {
	c := Point{x: 2, y: 3}
	r := c.Add(4)
	return r
}

func UseAddWithLiteral() uint64 {
	r := Point{x: 2, y: 3}.Add(4)
	return r
}

func (Point) IgnoreReceiver() string {
	return "ok"
}
