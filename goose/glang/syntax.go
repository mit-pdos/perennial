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

// FuncImpl is the name of the GooseLang implementation of a function (the
// function's own name is a GoString naming it).
func FuncImpl(name string) string {
	return GoName(name) + ".impl"
}

type Expr interface {
	// Lean converts the expression to Lean, either as a Lean term or as a
	// GooseLang expr (see lean.go)
	Lean(m LeanMode) string
}

// The Lean names of Go identifiers. Each kind of name has one rule:
//
//   - a struct field F is the projection F' (see recordProjection);
//   - a name goose binds inside a declaration, a type parameter or a
//     function-local constant P, is P₀ (and a type parameter's value type is
//     P₀'; see BinderName);
//   - every other Go name X (a type, function, global or method) is
//     GoName(X): X, or X'' when X is reserved (see reservedName). Lean
//     keywords are reserved like every other conflicting name: Go `type Type
//     int64` is `Type''`, `def` is `def''`, `Int` is `Int''`; the field `Type`
//     is `Type'`;
//   - a generated name derived from a Go name x (a class member or an
//     instance) is tag'x (see MemberName): get'F, unfold'M, instance'T,
//     typed_pointsto'T, access_load'T'F, ...
//
// Guillemets are only a lexing fallback, not a conflict rule: a Go identifier
// may contain Unicode letters and digits that Lean's identifier lexer rejects
// (`é`, `名`, `λ`; Lean accepts ASCII letters, `_` and its letter-like ranges,
// such as most Greek letters), and such a name is written in guillemets
// (LeanQuoteComponent, conservatively for every non-ASCII name), which does
// not change the name.
//
// Why this is collision-free. Go identifiers contain no "'" and no subscript
// digit, so the four forms are disjoint: a name ending in exactly one "'"
// after a Go identifier is a field projection (or P₀', a value binder); one
// ending in "''" is a reserved Go name; one containing ₀ is a binder; one with
// a "'" before its end is a generated name, whose fixed tag (no "'") and Go
// name it determines. So a field projection S.F' or a class member in scope
// can never capture a type, function, global or method, a binder never
// captures a package-level name, and no two generated names coincide. Every
// other name the output refers to unqualified (framework, Iris and Lean names,
// the generated code's own binders) is reserved, so no Go name takes it;
// TestOutputNamesReserved checks that against the outputs of goose's test
// packages.

// reservedNames are the Lean names a Go name (other than a field) must not
// take; GoName renames such a Go name X to X”. A Lean declaration named
// `A.b` is elaborated inside namespace A, so the names goose (and Lean)
// declares under a Go name's namespace would capture a same-named Go name
// referenced there; and a Go name in the package's namespace would capture a
// same-named framework name the output refers to unqualified. reservedName
// also covers the name shapes listed there.
var reservedNames = map[string]bool{}

func init() {
	// framework names the Lean printer emits unqualified (GooseLang
	// constructors and Golang/Defn definitions), and Lean names the generated
	// code refers to unqualified
	for _, w := range strings.Fields(`Val Var Rec App If Pair Fst Snd Fork Lam
	Let Seq LamV RecV PairV LitV BAnon BNamed GoInstruction GoOp GoUnOp GoLoad
	GoStore GoAlloc GoZeroVal FuncResolve MethodResolve StructFieldGet
	StructFieldRef StructFieldSet GlobalVarAddr Index IndexRef Slice FullSlice
	TypeAssert TypeAssert2 Convert CompositeLiteral SelectStmt LiteralValue
	KeyedElement KeyField KeyInteger KeyExpression ElementExpression ElementLiteralValue
	SelectStmtClauses CommClause SendCase RecvCase UntypedNil into_val
	exception_seq do_execute do_return exception_do do_break do_continue do_for
	wrap_defer deferType none some None Some W64 W32 W16 W8 w64 w32 w16 w8 Int Bool Unit
	List go_string val loc slice array chan interface func pkg_id under
	FuncUnfold MethodUnfold TypeRepr EqualsUnfold ZeroVal zero_val_def
	PkgInfo GoEquals GoLt GoLe GoGt GoGe GoPlus GoSub GoMul GoDiv GoRemainder
	GoAnd GoOr GoXor GoBitClear GoShiftl GoShiftr GoPos GoNeg GoNot GoComplement
	struct_field_ref intoVal exceptionSeq doExecute doReturn exceptionDo doBreak
	doContinue doFor catchBreak wrapDefer wrapDeferRecover recoverPanic GoString Loc zeroValDef structFieldRef
	Set is mod lookup list True False`) {
		reservedNames[w] = true
	}
	// the names goose declares under a Go name's namespace X: X.ty,
	// X.underlying, X.fields, X.fieldsUnsealed, X.zero_val, X.TypeAssumptions
	// (types), X.impl (functions, methods); the package's Assumptions class;
	// the fixed members of the TypeAssumptions classes, which are in scope as
	// locals in the later members' types
	for _, w := range strings.Fields(`ty underlying fields fieldsUnsealed zero_val
	TypeAssumptions impl Assumptions type_repr isUnderlying method_set ptr_method_set`) {
		reservedNames[w] = true
	}
	// the names Lean declares under a structure or class X (X.mk, X.rec, ...)
	// and the reserved names of a definition X (X.eq_def, X.eq_1, ...; see
	// Lean.isReservedName), which name resolution finds like declarations
	for _, w := range strings.Fields(`mk rec recOn casesOn noConfusion
	noConfusionType ctorIdx _sizeOf_1 _sizeOf_inst eq_def eq_unfold fun_cases
	fun_cases_unfolding
	congr_simp`) {
		reservedNames[w] = true
	}
	// framework, Iris and Lean names the generated code and proofs refer to
	// unqualified (TestOutputNamesReserved checks this list against the
	// outputs of the test packages): the value types of Go values (a Go type
	// `GoSlice` used as a field type would otherwise be captured), the
	// semantics' classes and contexts, the proof classes and tactics, Lean's
	// literals, and the options and attributes of the generated files
	for _, w := range strings.Fields(`GoSlice GoChan GoFunc GoMap GoError GoInterface
	GoArray GooseExts GoGlobalContext GoLocalContext GoSemanticsFunctions
	GooseSemantics GooseInterp doBreakTo doContinueTo catchLabel Classical
	Nonempty NonemptyType mkRat true false PROP TypedPointsto typedPointsto
	typedPointstoDef typedPointstoDef_dfractional typedPointstoDef_timeless
	typedPointsto_agree AccessStrict DFrac IProp IntoValTyped
	IntoValTypedUnderlying HasLC HeapGS BundledGFunctors Iris iprop
	solve_into_val_typed_struct solve_pointsto_access_struct
	solve_typed_pointsto_agree solve_typed_pointsto_dfractional
	solve_typed_pointsto_timeless rfl unfold _root_ expose irreducible reducible
	linter autoImplicit maxHeartbeats maxRecDepth pkgImportedPkgs string`) {
		reservedNames[w] = true
	}
	// the binders and section variables of the generated code and proofs,
	// which would capture a same-named Go name in their scope
	for _, w := range strings.Fields(`x y l v dq hlc GF hG go_gctx sem sem_fn pre_sem`) {
		reservedNames[w] = true
	}
}

// reservedName reports whether a Go name must be renamed by GoName: it is a
// Lean keyword, is in reservedNames, or is one of Lean's equation lemma names
// X.eq_<n>.
func reservedName(x string) bool {
	if strings.Contains(x, "'") {
		// not a Go identifier: a generated name, or one GoName renamed
		return false
	}
	if reservedNames[x] || LeanKeywords[x] {
		// LeanKeywords: Lean's tokens, which an identifier must not be
		return true
	}
	if n, ok := strings.CutPrefix(x, "eq_"); ok && n != "" && strings.Trim(n, "0123456789") == "" {
		return true
	}
	return false
}

// BinderName is the Lean name of a Go name that goose binds inside a
// declaration rather than declares: a type parameter p (its go.GoType binder
// and, in a model structure, its Type parameter; its value type is the binder
// p₀') and a function-local constant (a `let`). It is p₀: Go identifiers
// cannot contain a subscript digit (Unicode category No), so no other
// Go-derived name is p₀ or p₀', and such a binder cannot capture a
// package-level or framework name referenced in its scope (Go `type U = T;
// type Box[T any] struct{ u U }`; a local `const Val = 1`), nor can the
// fields F' of a structure capture its parameters.
func BinderName(p string) string {
	return p + "₀"
}

// MemberName is the name of a generated declaration or class member derived
// from a Go name x: tag'x (get'F, set'F, unfold'M, ptr_unfold'M, instance'T,
// unfold'f, import'p, equals_unfold'T). The tags contain no "'" and Go names
// none, so the name determines its tag and Go name (no two members collide),
// and it is never a Go-derived name (which has "'" only at its end), so a
// member in scope cannot capture a Go name or be captured by one.
func MemberName(tag, x string) string {
	return tag + "'" + x
}

// GoName is the Lean name of a Go identifier that is not a struct field: x,
// or x” if x is reserved (see reservedName). It is idempotent.
func GoName(x string) string {
	if reservedName(x) {
		return x + "''"
	}
	return x
}

// TermIdent is a possibly qualified identifier of a Lean term (see LeanIdent).
type TermIdent string

// VerbatimExpr is translated literally.
type VerbatimExpr string

// GenericTypeExpr is the type of an axiomatized generic type with type
// parameters Params: a function from go.GoType arguments to a go.GoType.
type GenericTypeExpr struct {
	Params []string
}

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

// CatchBreakExpr runs a switch or select statement (Body) whose case bodies
// break out of it: a break outcome becomes a normal one.
type CatchBreakExpr struct {
	Body Expr
}

// BreakToExpr is `break Label`, ContinueToExpr is `continue Label`.
type BreakToExpr struct {
	Label string
}

type ContinueToExpr struct {
	Label string
}

// CatchLabelExpr runs the body of a loop, or a switch or select statement
// (Body), labeled Label: a `break Label` outcome becomes a break, and a
// `continue Label` outcome a continue.
type CatchLabelExpr struct {
	Label string
	Body  Expr
}

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

// ForRangeArrayExpr is a range loop over an array of length Len, or a pointer
// to one (Ptr). Without Array, it only counts the indices: the elements are
// not read, and Body only binds the key.
type ForRangeArrayExpr struct {
	Len   int64
	Elem  Expr
	Ptr   bool
	Array Expr // nil: indices only
	Body  Expr
}

// ForRangeStringExpr is a range loop over the runes of a string.
type ForRangeStringExpr struct {
	String Expr
	Body   Expr
}

type ForRangeChanExpr struct {
	Chan Expr
	Elem Expr
	Body Expr
}

// ForRangeFuncExpr is a range loop over a function Func whose yield function
// has Arity parameters (at most 2).
type ForRangeFuncExpr struct {
	Arity int
	Func  Expr
	Body  Expr
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
	// the function takes the cell recover() reads as a parameter `$recover`,
	// after the receiver
	RecoverArg bool
	Args       []Binder
	Body       Expr
	Comment    string
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

// TypeMethod is the name of the GooseLang implementation of a method.
func TypeMethod(typeName string, methodName string) string {
	return fmt.Sprintf("%s.%s.impl", GoName(typeName), GoName(methodName))
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
	// Chunks are the other modules of a package whose translation is split
	// over several modules, by name (chunkN, in the package's directory).
	Chunks map[string]File
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

// IsReservedName reports whether GoName renames x (for tests).
func IsReservedName(x string) bool { return reservedName(x) }
