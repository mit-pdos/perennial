package interfacerecursion

type A interface {
	Foo()
}

type B interface {
	Bar()
}

type c struct { // ERROR cycle in dependencies
}

func (c *c) Foo() {
	var y B = c
	y.Bar()
}

func (c *c) Bar() {
	var y A = c
	y.Foo()
}
