package glang

// The GooseLang syntax produced by the translator. lean.go prints it.

import (
	"fmt"
	"math/big"
	"strings"
)

func indent(spaces int, s string) string {
	lines := strings.Split(s, "\n")
	indentation := strings.Repeat(" ", spaces)
	for i, line := range lines {
		if i == 0 || line == "" {
			continue
		}
		lines[i] = indentation + line
	}
	return strings.Join(lines, "\n")
}

func FuncImpl(name string) string {
	return name + "ⁱᵐᵖˡ"
}

type Expr interface {
	// Lean converts the expression to Lean, either as a Lean term or as a
	// GooseLang expr (see lean.go)
	Lean(m LeanMode) string
}

// primedNames are names that a Go identifier is renamed away from by adding a
// "'" suffix (see ToIdent): Lean keywords and framework names that the
// generated code refers to unqualified (see also LeanShadowNames).
var primedNames = map[string]bool{
	"Set":                 true,
	"Type":                true,
	"is":                  true,
	"as":                  true,
	"mod":                 true,
	"match":               true,
	"lookup":              true,
	"list":                true,
	"True":                true,
	"False":               true,
	"val":                 true,
	"go_string":           true,
	"deferType":           true,
	"GoAlloc":             true,
	"GoZeroVal":           true,
	"UntypedNil":          true,
	"GlobalVarAddr":       true,
	"None":                true,
	"Some":                true,
	"KeyedElement":        true,
	"CompositeLiteral":    true,
	"LiteralValue":        true,
	"ElementLiteralValue": true,
	"KeyField":            true,
	"KeyExpression":       true,
	"KeyInteger":          true,
	"FuncResolve":         true,
	"MethodResolve":       true,
	"StructFieldGet":      true,
	"StructFieldRef":      true,
	"FullSlice":           true,
	"Slice":               true,
	"IndexRef":            true,
	"Index":               true,
	"TypeAssert":          true,
	"TypeAssert2":         true,
	"Convert":             true,
	"SelectStmt":          true,
	"Fst":                 true,
	"Snd":                 true,
	"W64":                 true,
	"W32":                 true,
	"W16":                 true,
	"W8":                  true,
	"w64":                 true,
	"w32":                 true,
	"w16":                 true,
	"w8":                  true,
}

// ToIdent renames a (possibly qualified) identifier whose last component would
// clash with a keyword or framework name, by adding a "'" suffix.
func ToIdent(s string) string {
	base := s
	if i := strings.LastIndex(base, "."); i > 0 {
		base = base[i+1:]
	}
	if primedNames[base] || LeanShadowNames[base] {
		return s + "'"
	}
	return s
}

// TermIdent is a possibly qualified identifier of a Lean term (renamed away
// from keywords, see ToIdent).
type TermIdent string

// VerbatimExpr is translated literally.
type VerbatimExpr string

// A Go qualified identifier, which is translated to a qualified Lean
// identifier.
type PackageIdent struct {
	Package string
	Ident   string
}

type ParenExpr struct {
	Inner Expr
}

// IdentExpr is a GooseLang variable
type IdentExpr string

// TermString is a Lean string (a go_string)
//
// This is printed like a StringLiteral, but semantically quite different from
// an IdentExpr.
type TermString string

// CallExpr includes primitives and references to other functions.
type CallExpr struct {
	MethodName Expr
	Args       []Expr
}

// NewCallExpr is a convenience to construct a CallExpr statically, especially
// for a fixed number of arguments.
func NewCallExpr(name Expr, args ...Expr) CallExpr {
	if len(args) == 0 {
		args = []Expr{Tt}
	}
	return CallExpr{MethodName: name, Args: args}
}

// Append creates a new CallExpr with args appended.
//
// Does not modify e.
func (e CallExpr) Append(args ...Expr) CallExpr {
	e2 := CallExpr{
		MethodName: e.MethodName,
		Args:       append(append([]Expr{}, e.Args...), args...),
	}
	return e2
}

type ContinueExpr struct{}

type BreakExpr struct{}

type ReturnExpr struct {
	Value Expr
}

type DoExpr struct {
	Expr Expr
}

func NewDoSeq(e, cont Expr) SeqExpr {
	return SeqExpr{Expr: DoExpr{Expr: e}, Cont: cont}
}

type SeqExpr struct {
	Expr, Cont Expr
}

type LetExpr struct {
	// Names is a list to support anonymous and tuple-destructuring bindings.
	//
	// If Names is an empty list the binding is anonymous.
	Names   []string
	ValExpr Expr
	Cont    Expr
}

func (e LetExpr) isAnonymous() bool {
	return len(e.Names) == 0
}

// TermLetExpr produces a Lean let expression, for local declarations.
type TermLetExpr struct {
	Name    string
	ValExpr Expr
	Cont    Expr
}

// A StructLiteral represents a record literal construction using name fields.
type StructLiteral struct {
	Type Expr
	Elts []Expr
}

type GooseBoolLiteral bool

type BoolLiteral bool

// GooseLang unit value
type UnitLiteral struct{}

var Tt UnitLiteral = struct{}{}

type ZLiteral struct {
	Value *big.Int
}

func IntToZ(value int64) ZLiteral {
	return ZLiteral{Value: big.NewInt(int64(value))}
}

type StringLiteral struct {
	Value string
}

func NewStringVal(s string) Expr {
	return ToVal{Value: StringLiteral{Value: s}}
}

type Int64Val struct {
	Value Expr
}

type Int32Val struct {
	Value Expr
}

type Int16Val struct {
	Value Expr
}

type Int8Val struct {
	Value Expr
}

type ToVal struct {
	Value Expr
}

type OpId int
type BinOp struct {
	OpId
	Type Expr
}

// Constants for the supported binary and unary operators
const (
	OpPlus OpId = iota
	OpMinus
	OpEquals
	OpNotEquals
	OpLessThan
	OpGreaterThan
	OpLessEq
	OpGreaterEq

	OpMul
	OpQuot
	OpRem
	OpShl
	OpShr

	OpAnd
	OpAndNot
	OpOr
	OpXor
	OpLAnd
	OpLOr

	OpNot
)

type BinaryExpr struct {
	X  Expr
	Op BinOp
	Y  Expr
}

type UnaryOp struct {
	OpId
	Type Expr
}

type UnaryExpr struct {
	X  Expr
	Op UnaryOp
}

// TermNotExpr is boolean negation of a Lean term.
type TermNotExpr struct {
	X Expr
}

type NotExpr struct {
	X Expr
}

type TupleExpr []Expr

// ListExpr is a Lean list.
type ListExpr []Expr

type DerefExpr struct {
	X  Expr
	Ty Expr
}

type StoreStmt struct {
	Dst Expr
	Ty  Expr
	X   Expr
}

type IfExpr struct {
	Cond Expr
	Then Expr
	Else Expr
}

// The init statement must wrap the ForLoopExpr, so it can make use of bindings
// introduced there.
type ForLoopExpr struct {
	Cond Expr
	Post Expr
	// the body of the loop
	Body Expr
}

type ForRangeSliceExpr struct {
	Ty    Expr
	Slice Expr
	Body  Expr
}

type ForRangeChanExpr struct {
	Chan Expr
	Elem Expr
	Body Expr
}

// ForRangeMapExpr is a call to the map iteration helper.
type ForRangeMapExpr struct {
	KeyType, ElemType Expr
	// map to iterate over
	Map Expr
	// body of loop, with KeyIdent and ValueIdent as free variables
	Body Expr
}

// SpawnExpr is a call to Spawn a thread running a procedure.
//
// The body can capture variables in the environment.
type SpawnExpr struct {
	Body Expr
}

type Binder struct {
	Name string
}

// FuncLit is an unnamed function literal, consisting of its parameters and body.
type FuncLit struct {
	Args []Binder
	Body Expr
}

type ValueScoped struct {
	Value Expr
}

// FuncDecl declares a function, including its parameters and body.
type FuncDecl struct {
	Name string
	// Method receiver name (nil if not a method)
	RecvArg  *Binder
	TypeArgs []TermIdent
	Args     []Binder
	Body     Expr
	Comment  string
}

type ConstDecl struct {
	Name    string
	Val     Expr
	Type    Expr
	Comment string
}

// VerbatimDecl is a declaration emitted literally.
type VerbatimDecl struct {
	Content string
}

type AxiomDecl struct {
	DeclName string
	Type     Expr
}

// Decl is a FuncDecl, StructDecl, CommentDecl, or ConstDecl
type Decl interface {
	LeanDecl() string
}

func TypeMethod(typeName string, methodName string) string {
	return fmt.Sprintf("%s__%sⁱᵐᵖˡ", typeName, methodName)
}

// These will not end up in `File.Decls`, they are put into `File.Imports` by `translatePackage`.
type ImportDecl struct {
	Path string
}

// GoPathToIdentPath converts a Go package path to the "/"-separated path of
// the generated modules, by replacing "." and "-" with "_"
// (github.com/mit-pdos/go-journal becomes github_com/mit_pdos/go_journal).
func GoPathToIdentPath(p string) string {
	p = strings.ReplaceAll(p, ".", "_")
	p = strings.ReplaceAll(p, "-", "_")
	return p
}

type RecordField struct {
	Name  string
	Value Expr
}

// File represents a complete Lean file (a sequence of declarations).
type File struct {
	// Header comes after the imports and Footer at the end of the file.
	Header         string
	Footer         string
	PkgPath        string
	PreHeaderDecls []Decl
	Decls          []Decl
}

type CommCase interface {
	Expr
}

type SendCase struct {
	ElemType Expr
	Chan     Expr
	Value    Expr
}

type RecvCase struct {
	ElemType Expr
	Chan     Expr
}

type CommClause struct {
	Comm CommCase
	Body Expr
}

type SelectStmtClauses struct {
	Default Expr // nil for None
	Clauses []CommClause
}
