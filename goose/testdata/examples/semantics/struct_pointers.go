package semantics

type Bar struct {
	a uint64
	b uint64
}

// Foo contains a nested struct which is intended to be manipulated through a
// Foo pointer
type Foo struct {
	bar Bar
}

func (bar *Bar) mutate() {
	bar.a = 2
	bar.b = 3
}

func (foo *Foo) mutateBar() {
	foo.bar.mutate()
}

func testFooBarMutation() bool {
	x := Foo{bar: Bar{a: 0, b: 0}}
	x.mutateBar()
	return x.bar.a == 2
}
