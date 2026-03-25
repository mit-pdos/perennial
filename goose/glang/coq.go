package glang

import (
	"fmt"
	"io"
	"math/big"
	"path"
	"path/filepath"
	"strings"
)

func addParens(needs_paren bool, expr string) string {
	if needs_paren {
		return "(" + expr + ")"
	} else {
		return expr
	}
}

// buffer is a simple indenting pretty printer
type buffer struct {
	lines       []string
	indentLevel int
}

func (pp buffer) indentation() string {
	b := make([]byte, pp.indentLevel)
	for i := range b {
		b[i] = ' '
	}
	return string(b)
}

func (pp *buffer) appendLine(line string) {
	pp.lines = append(pp.lines, line)
}

func (pp *buffer) AddLine(line string) {
	if line == "" {
		pp.appendLine("")
	} else {
		pp.appendLine(pp.indentation() + indent(pp.indentLevel, line))
	}
}

// Add adds formatted to the buffer
func (pp *buffer) Add(format string, args ...interface{}) {
	pp.AddLine(fmt.Sprintf(format, args...))
}

func (pp *buffer) Indent(spaces int) {
	pp.indentLevel += spaces
}

func (pp *buffer) Block(prefix string, format string, args ...interface{}) int {
	pp.AddLine(prefix + indent(len(prefix), fmt.Sprintf(format, args...)))
	pp.Indent(len(prefix))
	return len(prefix)
}

func (pp buffer) Build() string {
	return strings.Join(pp.lines, "\n")
}

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

func (pp *buffer) AddComment(c string) {
	if c == "" {
		return
	}
	// these hacks ensure that Go comments don't insert stray Coq comments
	c = strings.ReplaceAll(c, "(*", "( *")
	c = strings.ReplaceAll(c, "*)", "* )")
	indent := pp.Block("(* ", "%s *)", c)
	pp.Indent(-indent)
}

func quote(s string) string {
	return `"` + s + `"`
}

// binder converts a Go name to a GooseLang binder
func binder(name string) string {
	// the Go ast uses "_" for ignored variables; convert this to GooseLang's "<>"
	// anonymous binder
	if name == "_" {
		return "<>"
	}
	return quote(name)
}

func FuncImpl(name string) string {
	return name + "ⁱᵐᵖˡ"
}

type Expr interface {
	// Coq converts the expression to a Coq string, wrapping with parens if needs_paren is true
	Coq(needs_paren bool) string
}

var GallinaKeywords map[string]bool = map[string]bool{
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

func ToIdent(s string) string {
	return GallinaIdent(s).Coq(false)
}

// GallinaIdent is treated as a possibly qualified Gallina identifier (and thus
// deconflicted with keywords).
type GallinaIdent string

func (e GallinaIdent) Coq(needs_paren bool) string {
	base := string(e)
	lastDotIndex := strings.LastIndex(base, ".")
	if lastDotIndex > 0 {
		base = base[lastDotIndex+1:]
	}
	if GallinaKeywords[string(base)] {
		e = e + "'"
	}
	return string(e)
}

// VerbatimExpr is translated literally to Coq.
type VerbatimExpr string

func (e VerbatimExpr) Coq(needs_paren bool) string {
	return string(e)
}

// A Go qualified identifier, which is translated to a Gallina qualified
// identifier.
type PackageIdent struct {
	Package string
	Ident   string
}

func (e PackageIdent) Coq(needs_paren bool) string {
	return fmt.Sprintf("%s.%s", ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(e.Package),
		ToIdent(e.Ident))
}

type ParenExpr struct {
	Inner Expr
}

func (e ParenExpr) Coq(needs_paren bool) string {
	return fmt.Sprintf("(%s)", e.Inner.Coq(needs_paren))
}

// IdentExpr is a go_lang-level variable
//
// An IdentExpr is quoted in Coq.
type IdentExpr string

func (e IdentExpr) Coq(needs_paren bool) string {
	return quote(string(e))
}

// GallinaString is a Gallina string, wrapped in quotes
//
// This is functionally identical to IdentExpr, but semantically quite
// different.
type GallinaString string

func (s GallinaString) Coq(needs_paren bool) string {
	return quote(string(s))
}

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

func (s CallExpr) Coq(needs_paren bool) string {
	comps := []string{s.MethodName.Coq(true)}

	for _, a := range s.Args {
		comps = append(comps, a.Coq(true))
	}
	return addParens(needs_paren, strings.Join(comps, " "))
}

type ContinueExpr struct{}

func (e ContinueExpr) Coq(needs_paren bool) string {
	return fmt.Sprintf("continue: #()")
}

type BreakExpr struct{}

func (e BreakExpr) Coq(needs_paren bool) string {
	return fmt.Sprintf("break: #()")
}

type ReturnExpr struct {
	Value Expr
}

func (e ReturnExpr) Coq(needs_paren bool) string {
	return fmt.Sprintf("return: %s", e.Value.Coq(needs_paren))
}

type DoExpr struct {
	Expr Expr
}

func (b DoExpr) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("do:  %s", b.Expr.Coq(true))
	return addParens(needs_paren, pp.Build())
}

func NewDoSeq(e, cont Expr) SeqExpr {
	return SeqExpr{Expr: DoExpr{Expr: e}, Cont: cont}
}

type SeqExpr struct {
	Expr, Cont Expr
}

func (b SeqExpr) Coq(needs_paren bool) string {
	var pp buffer

	if b.Cont == nil {
		pp.Add("%s", b.Expr.Coq(false))
		return addParens(needs_paren, pp.Build())
	}

	pp.Add("%s;;;", b.Expr.Coq(false))
	pp.Add("%s", b.Cont.Coq(false))
	return addParens(needs_paren, pp.Build())
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

func (b LetExpr) Coq(needs_paren bool) string {
	var pp buffer
	if b.Cont == nil {
		if !b.isAnonymous() {
			panic("let expr with nil cont but non-anonymous binding")
		}
		pp.Add("%s", b.ValExpr.Coq(false))
		return addParens(needs_paren, pp.Build())
	}

	if b.isAnonymous() {
		pp.Add("%s;;", b.ValExpr.Coq(false))
	} else if len(b.Names) == 1 {
		pp.Add("let: %s := %s in", binder(b.Names[0]), b.ValExpr.Coq(true))
	} else if len(b.Names) == 2 {
		pp.Add("let: (%s, %s) := %s in",
			binder(b.Names[0]),
			binder(b.Names[1]),
			b.ValExpr.Coq(true))
	} else if len(b.Names) == 3 {
		pp.Add("let: ((%s, %s), %s) := %s in",
			binder(b.Names[0]),
			binder(b.Names[1]),
			binder(b.Names[2]),
			b.ValExpr.Coq(true))
	} else if len(b.Names) == 4 {
		pp.Add("let: (((%s, %s), %s), %s) := %s in",
			binder(b.Names[0]),
			binder(b.Names[1]),
			binder(b.Names[2]),
			binder(b.Names[3]),
			b.ValExpr.Coq(true))
	} else if len(b.Names) == 5 {
		pp.Add("let: ((((%s, %s), %s), %s), %s) := %s in",
			binder(b.Names[0]),
			binder(b.Names[1]),
			binder(b.Names[2]),
			binder(b.Names[3]),
			binder(b.Names[4]),
			b.ValExpr.Coq(true))
	} else if len(b.Names) == 6 {
		pp.Add("let: (((((%s, %s), %s), %s), %s), %s) := %s in",
			binder(b.Names[0]),
			binder(b.Names[1]),
			binder(b.Names[2]),
			binder(b.Names[3]),
			binder(b.Names[4]),
			binder(b.Names[5]),
			b.ValExpr.Coq(true))
	} else if len(b.Names) == 7 {
		pp.Add("let: ((((((%s, %s), %s), %s), %s), %s), %s) := %s in",
			binder(b.Names[0]),
			binder(b.Names[1]),
			binder(b.Names[2]),
			binder(b.Names[3]),
			binder(b.Names[4]),
			binder(b.Names[5]),
			binder(b.Names[6]),
			b.ValExpr.Coq(true))
	} else {
		panic(fmt.Sprintf("no support for destructuring more than %d return values (up to 6 supported)", len(b.Names)))
	}
	pp.Add("%s", b.Cont.Coq(false))
	return addParens(needs_paren, pp.Build())
}

// GallinaLetExpr produces a Gallina let expression, for local declarations.
type GallinaLetExpr struct {
	Name    string
	ValExpr Expr
	Cont    Expr
}

func (b GallinaLetExpr) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("let %s := %s in", GallinaIdent(b.Name).Coq(false), b.ValExpr.Coq(true))
	pp.Add("%s", b.Cont.Coq(false))
	return addParens(needs_paren, pp.Build())
}

// A StructLiteral represents a record literal construction using name fields.
type StructLiteral struct {
	Type Expr
	Elts []Expr
}

func (sl StructLiteral) Coq(needs_paren bool) string {
	var pp buffer
	method := "CompositeLiteral"
	pp.Add("%s %s (", method, sl.Type.Coq(true))
	pp.Indent(2)
	pp.Add(`let: "$$vs" := go.StructElementListNil #() in `)
	for _, f := range sl.Elts {
		pp.Add(`let: "$$vs" := go.ElementListApp "$$vs" %s in`, f.Coq(true))
	}
	pp.Add(`"$$vs"`)
	pp.Indent(-2)
	pp.Add(")")
	return addParens(needs_paren, pp.Build())
}

type GooseBoolLiteral bool

func (b GooseBoolLiteral) Coq(needs_paren bool) string {
	if b {
		return "#true"
	} else {
		return "#false"
	}
}

type BoolLiteral bool

func (b BoolLiteral) Coq(needs_paren bool) string {
	if b {
		return "true"
	} else {
		return "false"
	}
}

// GooseLang unit value
type UnitLiteral struct{}

var Tt UnitLiteral = struct{}{}

func (tt UnitLiteral) Coq(needs_paren bool) string {
	return "#()"
}

type ZLiteral struct {
	Value *big.Int
}

func IntToZ(value int64) ZLiteral {
	return ZLiteral{Value: big.NewInt(int64(value))}
}

func (z ZLiteral) Coq(needs_paren bool) string {
	if needs_paren && z.Value.Sign() < 0 {
		return "(" + z.Value.String() + ")"
	} else {
		return z.Value.String()
	}
}

type StringLiteral struct {
	Value string
}

func (s StringLiteral) Coq(needs_paren bool) string {
	return fmt.Sprintf(`"%s"`, strings.Replace(s.Value, `"`, `""`, -1)) + "%go"
}

func NewStringVal(s string) Expr {
	return ToVal{Value: StringLiteral{Value: s}}
}

type Int64Val struct {
	Value Expr
}

func (l Int64Val) Coq(needs_paren bool) string {
	return fmt.Sprintf("#(W64 %s)", l.Value.Coq(true))
}

type Int32Val struct {
	Value Expr
}

func (l Int32Val) Coq(needs_paren bool) string {
	return fmt.Sprintf("#(W32 %s)", l.Value.Coq(true))
}

type Int16Val struct {
	Value Expr
}

func (l Int16Val) Coq(needs_paren bool) string {
	return fmt.Sprintf("#(W16 %s)", l.Value.Coq(true))
}

type Int8Val struct {
	Value Expr
}

func (l Int8Val) Coq(needs_paren bool) string {
	return fmt.Sprintf("#(W8 %s)", l.Value.Coq(true))
}

type ToVal struct {
	Value Expr
}

func (l ToVal) Coq(needs_paren bool) string {
	return fmt.Sprintf(`#%s`, l.Value.Coq(true))
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

var withTypeAnnotation = map[OpId]string{
	OpPlus:        "+",
	OpMinus:       "-",
	OpEquals:      "=",
	OpNotEquals:   "≠",
	OpMul:         "*",
	OpQuot:        "/",
	OpRem:         "%",
	OpLessThan:    "<",
	OpGreaterThan: ">",
	OpLessEq:      "≤",
	OpGreaterEq:   "≥",
	OpShl:         "<<",
	OpShr:         ">>",
	OpAnd:         "&",
	OpAndNot:      "&^",
	OpOr:          "|",
	OpXor:         "^",
	OpNot:         "!",
}

var withoutTypeAnnotation = map[OpId]string{
	OpLAnd: "&&",
	OpLOr:  "||",
}

func (o BinOp) renderOp() string {
	if op, ok := withTypeAnnotation[o.OpId]; ok {
		return op + "⟨" + o.Type.Coq(false) + "⟩"
	} else if op, ok := withoutTypeAnnotation[o.OpId]; ok {
		return op
	} else {
		panic(fmt.Sprint("unsupported op: ", o))
	}
}

type BinaryExpr struct {
	X  Expr
	Op BinOp
	Y  Expr
}

func (be BinaryExpr) Coq(needs_paren bool) string {
	expr := fmt.Sprintf("%s %s %s",
		be.X.Coq(true), be.Op.renderOp(), be.Y.Coq(true))
	return addParens(needs_paren, expr)
}

type UnaryOp struct {
	OpId
	Type Expr
}

func (o UnaryOp) renderOp() string {
	if op, ok := withTypeAnnotation[o.OpId]; ok {
		return "⟨" + o.Type.Coq(false) + "⟩" + op
	} else {
		panic(fmt.Sprint("unsupported unary op: ", o))
	}
}

type UnaryExpr struct {
	X  Expr
	Op UnaryOp
}

func (be UnaryExpr) Coq(needs_paren bool) string {
	expr := fmt.Sprintf("%s %s", be.Op.renderOp(), be.X.Coq(true))
	return addParens(needs_paren, expr)
}

type GallinaNotExpr struct {
	X Expr
}

func (e GallinaNotExpr) Coq(needs_paren bool) string {
	return fmt.Sprintf("(negb %s)", e.X.Coq(true))
}

type NotExpr struct {
	X Expr
}

func (e NotExpr) Coq(needs_paren bool) string {
	return fmt.Sprintf("(⟨go.bool⟩! %s)", e.X.Coq(true))
}

type TupleExpr []Expr

func (te TupleExpr) Coq(needs_paren bool) string {
	var comps []string
	for _, t := range te {
		comps = append(comps, t.Coq(false))
	}
	return fmt.Sprintf("(%s)",
		indent(1, strings.Join(comps, ", ")))
}

// ListExpr is a Gallina list.
type ListExpr []Expr

func (le ListExpr) Coq(needs_paren bool) string {
	var comps []string
	for _, t := range le {
		comps = append(comps, t.Coq(false))
	}
	elements := indent(1, strings.Join(comps, "; "))
	if strings.HasPrefix(elements, "#") {
		// [# ...] is a vector notation while we want the list notation [ ... ]
		// (and `[#` is a single token even if the vector notation isn't in
		// scope)
		return fmt.Sprintf("[ %s ]", elements)
	}
	return fmt.Sprintf("[%s]", elements)
}

type DerefExpr struct {
	X  Expr
	Ty Expr
}

func (e DerefExpr) Coq(needs_paren bool) string {
	expr := fmt.Sprintf("![%s] %s", e.Ty.Coq(false), e.X.Coq(true))
	return addParens(needs_paren, expr)
}

type StoreStmt struct {
	Dst Expr
	Ty  Expr
	X   Expr
}

func (e StoreStmt) Coq(needs_paren bool) string {
	expr := fmt.Sprintf("%s <-[%s] %s", e.Dst.Coq(true), e.Ty.Coq(false), e.X.Coq(true))
	return addParens(needs_paren, expr)
}

type IfExpr struct {
	Cond Expr
	Then Expr
	Else Expr
}

func flowBranch(pp *buffer, prefix string, e Expr, suffix string) {
	code := e.Coq(false) + suffix
	if !strings.ContainsRune(code, '\n') {
		// compact, single-line form
		indent := pp.Block(prefix+" ", "%s", code)
		pp.Indent(-indent)
		return
	}
	// full multiline, nicely indented form
	pp.AddLine(prefix)
	pp.Indent(2)
	pp.AddLine(code)
	pp.Indent(-2)
}

func (ife IfExpr) Coq(needs_paren bool) string {
	var pp buffer
	// Since we are parenthesesizing all if, we don't need to parenthesize the things inside the if
	pp.Add("(if: %s", ife.Cond.Coq(false))
	flowBranch(&pp, "then", ife.Then, "")
	flowBranch(&pp, "else", ife.Else, ")")
	return pp.Build()
}

// The init statement must wrap the ForLoopExpr, so it can make use of bindings
// introduced there.
type ForLoopExpr struct {
	Cond Expr
	Post Expr
	// the body of the loop
	Body Expr
}

func (e ForLoopExpr) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("(for: (λ: <>, %s); (λ: <>, %s) := λ: <>,", e.Cond.Coq(false), e.Post.Coq(false))
	pp.Indent(2)
	pp.Add("%s)", e.Body.Coq(false))
	return pp.Build()
}

type ForRangeSliceExpr struct {
	Ty    Expr
	Slice Expr
	Body  Expr
}

func (e ForRangeSliceExpr) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("slice.for_range %s %s (λ: \"$key\" \"$value\",",
		e.Ty.Coq(true),
		e.Slice.Coq(true),
	)
	pp.Indent(2)
	pp.Add("%s)", e.Body.Coq(false))
	pp.Indent(-2)
	return addParens(needs_paren, pp.Build())
}

type ForRangeChanExpr struct {
	Chan Expr
	Elem Expr
	Body Expr
}

func (e ForRangeChanExpr) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("chan.for_range %s %s (λ: \"$key\",",
		e.Elem.Coq(true),
		e.Chan.Coq(true),
	)
	pp.Indent(2)
	pp.Add("%s)", e.Body.Coq(false))
	pp.Indent(-2)
	return addParens(needs_paren, pp.Build())
}

// ForRangeMapExpr is a call to the map iteration helper.
type ForRangeMapExpr struct {
	KeyType, ElemType Expr
	// map to iterate over
	Map Expr
	// body of loop, with KeyIdent and ValueIdent as free variables
	Body Expr
}

func (e ForRangeMapExpr) Coq(needs_paren bool) string {
	var pp buffer
	pp.Add("map.for_range %s %s %s (λ: \"$key\" \"value\",", e.KeyType.Coq(true),
		e.ElemType.Coq(true), e.Map.Coq(true))
	pp.Indent(2)
	pp.Add("%s)", e.Body.Coq(false))
	return addParens(needs_paren, pp.Build())
}

// SpawnExpr is a call to Spawn a thread running a procedure.
//
// The body can capture variables in the environment.
type SpawnExpr struct {
	Body Expr
}

func (e SpawnExpr) Coq(needs_paren bool) string {
	var pp buffer
	pp.Block("Fork (", "%s)", e.Body.Coq(false))
	return addParens(needs_paren, pp.Build())
}

type Binder struct {
	Name string
}

func (b Binder) Coq(needs_paren bool) string {
	return binder(b.Name)
}

func bindings(args []string) string {
	if len(args) == 0 {
		return binder("_")
	}
	var binders []string
	for _, a := range args {
		binders = append(binders, binder(a))
	}
	return strings.Join(binders, " ")
}

func funcBinders(xs []Binder) string {
	var args []string
	for _, a := range xs {
		args = append(args, a.Name)
	}
	return bindings(args)
}

// FuncLit is an unnamed function literal, consisting of its parameters and body.
type FuncLit struct {
	Args []Binder
	Body Expr
}

func (e FuncLit) Coq(needs_paren bool) string {
	var pp buffer

	pp.Add("(λ: %s,", funcBinders(e.Args))
	pp.Indent(2)
	defer pp.Indent(-2)
	pp.AddLine(e.Body.Coq(false))
	pp.Add(")")

	return pp.Build()
}

type ValueScoped struct {
	Value Expr
}

func (e ValueScoped) Coq(needs_paren bool) string {
	return e.Value.Coq(true) + "%V"
}

// FuncDecl declares a function, including its parameters and body.
type FuncDecl struct {
	Name string
	// Method receiver name (nil if not a method)
	RecvArg  *Binder
	TypeArgs []GallinaIdent
	Args     []Binder
	Body     Expr
	Comment  string
}

// Signature renders the function declaration's bindings
func (d FuncDecl) Signature() string {
	var args []string
	if d.RecvArg != nil {
		args = append(args, d.RecvArg.Coq(false))
	}
	for _, a := range d.Args {
		args = append(args, a.Coq(false))
	}
	// note we systematically take a unit argument, even for methods that have a
	// receiver
	if len(d.Args) == 0 {
		args = append(args, binder("_"))
	}
	return strings.Join(args, " ")
}

const declImplicitParams = "{ext : ffi_syntax} {go_gctx : GoGlobalContext}"

// CoqDecl implements the Decl interface
//
// For FuncDecl this emits the Coq vernacular Definition that defines the whole
// function.
func (d FuncDecl) CoqDecl() string {
	var pp buffer
	pp.AddComment(d.Comment)

	typeParams := ""
	if len(d.TypeArgs) > 0 {
		typeParams = " ("
		for _, a := range d.TypeArgs {
			typeParams = typeParams + a.Coq(false) + " "
		}
		typeParams = typeParams + ": go.type)"
	}

	pp.Add("Definition %s %s%s : val :=",
		GallinaIdent(d.Name).Coq(false), declImplicitParams, typeParams)
	func() {
		pp.Indent(2)
		defer pp.Indent(-2)
		pp.Add("λ: %s,", d.Signature())
		pp.Indent(2)
		defer pp.Indent(-2)
		pp.AddLine(d.Body.Coq(false) + ".")
	}()
	return pp.Build()
}

type ConstDecl struct {
	Name    string
	Val     Expr
	Type    Expr
	Comment string
}

func (d ConstDecl) CoqDecl() string {
	var pp buffer
	pp.AddComment(d.Comment)
	indent := pp.Block("Definition ", "%s %s : %s := %s.",
		GallinaIdent(d.Name).Coq(false), declImplicitParams, d.Type.Coq(false), d.Val.Coq(false))
	pp.Indent(-indent)
	return pp.Build()
}

// VerbatimDecl is translated literally as a Coq declaration.
type VerbatimDecl struct {
	Content string
}

func (e VerbatimDecl) CoqDecl() string {
	return e.Content
}

type AxiomDecl struct {
	DeclName string
	Type     Expr
}

func (d AxiomDecl) CoqDecl() string {
	return fmt.Sprintf("Axiom %s : ∀ %s, %s.",
		GallinaIdent(d.DeclName).Coq(false), declImplicitParams, d.Type.Coq(false))
}

// Decl is a FuncDecl, StructDecl, CommentDecl, or ConstDecl
type Decl interface {
	CoqDecl() string
}

func TypeMethod(typeName string, methodName string) string {
	return fmt.Sprintf("%s__%sⁱᵐᵖˡ", typeName, methodName)
}

// The header to use normally (replaced only if bootstrapping).
const DefaultHeader string = `From New.golang Require Import defn.`

// The bootstrap import header if using a minimal list of imports.
const BootstrapHeader string = `From New.golang Require Import defn.pre.`

// These will not end up in `File.Decls`, they are put into `File.Imports` by `translatePackage`.
type ImportDecl struct {
	Path string
}

// This is an injective mapping
// FIXME: should really use this
func goPathToCoqPath(p string) string {
	p = strings.ReplaceAll(p, "_", "__")
	p = strings.ReplaceAll(p, ".", "_dot_")
	p = strings.ReplaceAll(p, "-", "_dash_")
	return p
}

func ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(p string) string {
	p = strings.ReplaceAll(p, "_", "_")
	p = strings.ReplaceAll(p, ".", "_")
	p = strings.ReplaceAll(p, "-", "_")
	return p
}

// ImportToPath converts a Go import path to a Coq path
func ImportToPath(pkgPath string) string {
	coqPath := ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkgPath)
	p := path.Dir(coqPath)
	filename := path.Base(coqPath) + ".v"
	return filepath.Join(p, filename)
}

func (decl ImportDecl) CoqDecl() string {
	coqImportQualid := strings.ReplaceAll(ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(decl.Path), "/", ".")
	return fmt.Sprintf("Require Export New.code.%s.", coqImportQualid)
}

type RecordField struct {
	Name  string
	Value Expr
}

// File represents a complete Coq file (a sequence of declarations).
type File struct {
	Header         string
	Footer         string
	PkgPath        string
	PreHeaderDecls []Decl
	Decls          []Decl
}

// Write outputs the Coq source for a File.
// noinspection GoUnhandledErrorResult
func (f File) Write(w io.Writer) {
	fmt.Fprintf(w, "(* autogenerated from %s *)\n", f.PkgPath)

	for _, d := range f.PreHeaderDecls {
		fmt.Fprintln(w, d.CoqDecl())
	}

	fmt.Fprintln(w, f.Header)
	fmt.Fprintln(w)

	for i, d := range f.Decls {
		fmt.Fprintln(w, d.CoqDecl())
		if i != len(f.Decls)-1 {
			fmt.Fprintln(w)
		}
	}
	fmt.Fprint(w, f.Footer)
}

type CommCase interface {
	Expr
}

type SendCase struct {
	ElemType Expr
	Chan     Expr
	Value    Expr
}

func (s SendCase) Coq(needs_paren bool) string {
	return fmt.Sprintf("(SendCase %s %s %s)", s.ElemType.Coq(true), s.Chan.Coq(true), s.Value.Coq(true))
}

type RecvCase struct {
	ElemType Expr
	Chan     Expr
}

func (s RecvCase) Coq(needs_paren bool) string {
	return fmt.Sprintf("(RecvCase %s %s)", s.ElemType.Coq(true), s.Chan.Coq(true))
}

type CommClause struct {
	Comm CommCase
	Body Expr
}

func (c CommClause) Coq(needs_paren bool) string {
	return fmt.Sprintf("(CommClause %s %s)", c.Comm.Coq(true), c.Body.Coq(true))
}

type SelectStmtClauses struct {
	Default Expr // nil for None
	Clauses []CommClause
}

func (s SelectStmtClauses) Coq(needs_paren bool) string {
	var def string
	if s.Default == nil {
		def = "None"
	} else {
		def = fmt.Sprintf("(Some %s)", s.Default.Coq(true))
	}

	var clauses []string
	for _, c := range s.Clauses {
		clauses = append(clauses, c.Coq(false))
	}
	list := "[" + strings.Join(clauses, "; ") + "]"

	return addParens(needs_paren, fmt.Sprintf("SelectStmtClauses %s %s", def, list))
}
