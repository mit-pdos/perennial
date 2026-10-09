package glang

// This file has the structs to represent types

type TypeDecl struct {
	Name       string
	Body       Expr
	TypeParams []string
	// a type alias (reducible, so instances for the aliased type apply)
	Alias bool
}

func (d TypeDecl) DefName() (bool, string) {
	return true, d.Name
}

// FieldDecl is a name:type declaration in a struct definition
type FieldDecl struct {
	Name     string
	Embedded bool
	Type     Expr
}

type StructType struct {
	Fields []FieldDecl
}

var _ Expr = StructType{}
