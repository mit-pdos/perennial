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
	// keywords are reserved like any other conflicting name
	assert.Equal("Type''", LeanIdent("Type"))
	assert.Equal("end''", LeanIdent("end"))
	assert.Equal("Type''.underlying", LeanIdent(TypeImpl("Type")))
	assert.Equal("def''.impl", LeanIdent(FuncImpl("def")))
	assert.Equal("T.match''.impl", LeanIdent(TypeMethod("T", "match")))
	// guillemets only where Lean cannot lex the identifier
	assert.Equal("«é»", LeanIdent("é"))
	assert.Equal("«λ''»", LeanIdent("λ"))
	// reserved names get "''", in every name built from them
	assert.Equal("lookup''", LeanIdent("lookup"))
	assert.Equal("Pair''", LeanIdent("Pair"))
	assert.Equal("Pair''.underlying", LeanIdent(TypeImpl("Pair")))
	assert.Equal("Pair''.TypeAssumptions", LeanIdent("Pair'assumptions"))
	assert.Equal("Pair''.fields", LeanIdent("Pair'fds"))
	assert.Equal("Index''.impl", LeanIdent(FuncImpl("Index")))
	assert.Equal("ty''.M.impl", LeanIdent(TypeMethod("ty", "M")))
	assert.Equal("_root_.Perennial.math.big.Int''", LeanIdent("_root_.Perennial.math.big.Int"))
	// a Go name that looks like a generated one is not decoded
	assert.Equal("Foo_Assumptions", LeanIdent("Foo_Assumptions"))
	// unreserved names are unchanged; method names follow the same rule
	assert.Equal("Foo.impl", LeanIdent(FuncImpl("Foo")))
	assert.Equal("T.M.impl", LeanIdent(TypeMethod("T", "M")))
	assert.Equal("T.Index''.impl", LeanIdent(TypeMethod("T", "Index")))
	assert.Equal("«_».impl", LeanIdent(FuncImpl("_")))
	assert.Equal("T.underlying", LeanIdent(TypeImpl("T")))
	assert.Equal("go.GoType.Named", LeanIdent("go.Named"))
	assert.Equal("go.uint64", LeanIdent("go.uint64"))
	assert.Equal("T'", LeanIdent("T'"))
}

func TestGoName(t *testing.T) {
	assert := assert.New(t)
	for _, x := range []string{"Val", "Int", "x", "ty", "underlying", "impl", "mk",
		"rec", "eq_def", "eq_1", "eq_23", "fun_cases_unfolding", "Assumptions", "GF",
		"GoSlice", "GoMap", "GooseExts", "TypedPointsto",
		"Type", "def", "fun", "at", "end", "Sort", "Prop", "match", "as", "λ"} {
		assert.Equal(x+"''", GoName(x), x)
		// idempotent
		assert.Equal(x+"''", GoName(GoName(x)), x)
	}
	// generated member shapes are not reserved: members are tag'x (MemberName)
	for _, x := range []string{"get_a", "set_a", "a_unfold", "ptr_a_unfold", "A_instance",
		"import_p_Assumption", "equals_unfold_S", "get", "set", "T", "Foo", "unfolded", "eq_", "eq_x", "getter", "init"} {
		assert.Equal(x, GoName(x), x)
	}
}

func TestMemberAndBinderNames(t *testing.T) {
	assert := assert.New(t)
	// field `unfold` vs method `get`; methods `ptr_f` and `f`
	assert.NotEqual(MemberName("get", "unfold"), MemberName("unfold", "get"))
	assert.NotEqual(MemberName("unfold", "ptr_f"), MemberName("ptr_unfold", "f"))
	assert.Equal("get'Type", LeanQuoteComponent(MemberName("get", "Type")))
	assert.Equal("T₀", LeanIdent(BinderName("T")))
	assert.Equal("x₀'", LeanIdent(BinderName("x")+"'"))
}
