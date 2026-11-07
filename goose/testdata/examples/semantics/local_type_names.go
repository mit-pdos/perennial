package semantics

type Type int64

type IntOrString struct {
	Type Type
}

func testLocalTypeNameShadow() bool {
	x := IntOrString{Type: Type(7)}
	x.Type = Type(9)
	return x.Type == Type(9)
}
