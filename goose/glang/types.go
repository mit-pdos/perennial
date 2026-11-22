package glang

// This file has the structs to represent types

type TypeDecl struct {
	Name string
	// nil: an opaque descriptor
	Body       Expr
	TypeParams []string
	// a type alias (reducible, so instances for the aliased type apply)
	Alias bool
}

func (d TypeDecl) DefName() (bool, string) {
	return true, d.Name
}

// FieldDecl is a name:type declaration in a struct definition. Tag is the
// field's tag, written only for an unnamed struct type (whose identity it is
// part of), "" when it has none.
type FieldDecl struct {
	Name     string
	Embedded bool
	Type     Expr
	Tag      string
}

type StructType struct {
	Fields []FieldDecl
}

var _ Expr = StructType{}
