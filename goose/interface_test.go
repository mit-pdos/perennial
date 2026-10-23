package goose

import (
	"strings"
	"testing"

	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/stretchr/testify/assert"
)

func TestLeanChunks(t *testing.T) {
	assert := assert.New(t)
	decl := func(s string) glang.Decl { return glang.VerbatimDecl{Content: s} }
	class := func(s string, fields int) glang.Decl {
		return typeAssumptionsDecl{VerbatimDecl: glang.VerbatimDecl{Content: s}, fields: fields}
	}
	pkgClass := packageAssumptionsDecl{glang.VerbatimDecl{Content: "Assumptions"}}

	// a small package stays in one module
	f := glang.File{PkgPath: "example.com/p", Decls: []glang.Decl{decl("a"), class("A", 10), pkgClass}}
	leanChunks(&f)
	assert.Nil(f.Chunks)
	assert.Len(f.Decls, 3)

	f = glang.File{
		PkgPath: "example.com/p",
		Header:  "public import Perennial.Golang.Defn\n",
		Footer:  "footer",
		Decls: []glang.Decl{decl("a"), class("A", 700), decl("b"), class("B", 300),
			class("C", 10), decl("c"), pkgClass},
	}
	leanChunks(&f)
	assert.Equal([]glang.Decl{decl("a"), decl("b"), decl("c")}, f.Chunks["chunk0"].Decls)
	assert.Equal("public import Perennial.Golang.Defn\n", f.Chunks["chunk0"].Header)
	assert.Equal([]glang.Decl{class("A", 700)}, f.Chunks["chunk1"].Decls)
	assert.Equal([]glang.Decl{class("B", 300), class("C", 10)}, f.Chunks["chunk2"].Decls)
	assert.Len(f.Chunks, 3)
	assert.True(strings.HasPrefix(f.Chunks["chunk2"].Header,
		"public import Perennial.Code.example_com.p.chunk0\n\n"))
	assert.Equal("footer", f.Chunks["chunk2"].Footer)
	assert.Equal([]glang.Decl{pkgClass}, f.Decls)
	assert.True(strings.HasPrefix(f.Header,
		"public import Perennial.Code.example_com.p.chunk0\n"+
			"public import Perennial.Code.example_com.p.chunk1\n"+
			"public import Perennial.Code.example_com.p.chunk2\n\n"))
}
