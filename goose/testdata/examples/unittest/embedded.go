package unittest

type embedA struct {
	a string
}

type embedB struct {
	embedA
}

type embedC struct {
	*embedB
}

type embedD struct {
	embedC
}

func (a embedA) Foo() string {
	return "embedA.Foo()"
}

func (a embedB) Foo() string {
	return "embedB.Foo()"
}

func (a *embedA) Bar() string {
	return "*embedA.Bar()"
}

func (a *embedB) Car() string {
	return "*embedB.Car()"
}

func returnEmbedVal() embedB {
	return embedB{}
}

func returnEmbedValWithPointer() embedD {
	return embedD{}
}

func useEmbeddedField(d embedD) string {
	x := d.a
	x = d.embedB.a
	d.a = "a1"

	y := &embedD{}
	y.a = "a2"

	return x
}

func useEmbeddedValField() string {
	x := returnEmbedVal().a
	x = returnEmbedValWithPointer().a
	return x
}

func useEmbeddedMethod(d embedD) bool {
	return d.Bar() == d.embedA.Bar()
}

func useEmbeddedMethod2(d embedD) bool {
	d.Car()
	return d.Foo() == d.embedB.Foo()
}
