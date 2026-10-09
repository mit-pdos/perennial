package glang

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestImportToLeanPath(t *testing.T) {
	assert.Equal(t, "github_com/mit_pdos/go_journal.lean",
		ImportToLeanPath("github.com/mit-pdos/go-journal"))
}

func TestLeanIdent(t *testing.T) {
	assert := assert.New(t)
	assert.Equal("lookup'", LeanIdent("lookup"))
	assert.Equal("Foo.impl", LeanIdent(FuncImpl("Foo")))
	assert.Equal("T.M.impl", LeanIdent(TypeMethod("T", "M")))
	assert.Equal("«_».impl", LeanIdent(FuncImpl("_")))
	assert.Equal("T.underlying", LeanIdent(TypeImpl("T")))
	assert.Equal("go.GoType.Named", LeanIdent("go.Named"))
	assert.Equal("«end»", LeanIdent("end"))
}

func TestLeanFfiPrelude(t *testing.T) {
	assert.Equal(t, "GrovePrelude", LeanFfiPrelude("grove"))
}
