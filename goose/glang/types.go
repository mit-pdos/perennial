package glang

// This file has the structs to represent types

import (
	"fmt"
)

type TypeDecl struct {
	Name       string
	Body       Expr
	TypeParams []string
}

func (d TypeDecl) CoqDecl() string {
	var pp buffer

	typeParams := ""
	for _, t := range d.TypeParams {
		typeParams += fmt.Sprintf(" (%s : go.type)", t)
	}

	pp.Add("Definition %s %s%s : go.type := %s.", GallinaIdent(d.Name).Coq(false), declImplicitParams, typeParams, d.Body.Coq(false))
	return pp.Build()
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

func (d StructType) CoqFields(indent int) string {
	var pp buffer
	pp.Indent(indent)
	for i, fd := range d.Fields {
		sep := ";"
		if i == len(d.Fields)-1 {
			sep = ""
		}
		fdcons := "go.FieldDecl"
		if fd.Embedded {
			fdcons = "go.EmbeddedField"
		}
		pp.Add("(%s %s %s)%s", fdcons,
			StringLiteral{fd.Name}.Coq(true),
			fd.Type.Coq(true), sep)
	}
	pp.Indent(-indent)
	return pp.Build()
}

func (d StructType) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("go.StructType [")
	pp.Add("%s", d.CoqFields(2))
	pp.AddLine("]")
	return addParens(needs_paren, pp.Build())
}
