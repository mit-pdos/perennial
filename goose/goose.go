// Package goose implements conversion from Go source to Perennial definitions.
//
// The exposed interface allows converting individual files as well as whole
// packages to a single Coq Ast with all the converted definitions, which
// include user-defined structs in Go as Coq records and a Perennial procedure
// for each Go function.
//
// See the Goose README at https://github.com/mit-pdos/perennial/goose for a high-level
// overview. The source also has some design documentation at
// https://github.com/mit-pdos/perennial/goose/tree/master/docs.
package goose

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"iter"
	"log"
	"math"
	"math/big"
	"path/filepath"
	"slices"
	"strconv"
	"strings"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/mit-pdos/perennial/goose/util"
	"github.com/mit-pdos/perennial/goose/util/toposort"
	"golang.org/x/tools/go/packages"
)

type outputDecls struct {
	importDecls    []glang.Decl
	typeNamedDecls []glang.Decl
	typeAliasDecls []glang.Decl
	constDecls     []glang.Decl
	varDecls       []glang.Decl
	funcDecls      []glang.Decl
	funcImplDecls  []glang.Decl
	finalDecls     []glang.Decl
}

func (o *outputDecls) decls() []glang.Decl {
	return slices.Concat(
		o.typeNamedDecls,
		o.typeAliasDecls,
		o.constDecls,
		o.varDecls,
		o.funcDecls,
		o.funcImplDecls,
		o.finalDecls,
	)
}

func (o *outputDecls) preHeaderDecls() []glang.Decl {
	return o.importDecls
}

// Ctx is a context for resolving Go code's types and source code
type Ctx struct {
	info    *types.Info
	pkgPath string

	// XXX: Initially tried using `pkg.Name` as the Gallina identifier holding
	// the full package path, but that doesn't work in a `package main` with a `func main`.
	// In that case, as soon as `func main` is defined inside `Module main.`,
	// reference to simply `main` (which should be the go_string holding the
	// package path) end up referring to the function. So, this uses `filename +
	// "." + pkg.Name` to refer to the Gallina definition that holds a package's
	// full path as a go_string (e.g. in `globals_test`, instead of `func_call #main ...`,
	// this results in `func_call #globals_test.main ...`).
	pkgIdent string
	errorReporter

	declImplicitParams string

	// XXX: this is so we can determine the expected return type when handling a
	// `returnStmt` so the appropriate conversion is inserted
	curFuncType   *types.Signature
	defaultReturn glang.Expr // this handles

	// Should be set to true when encountering a defer statement in the body of
	// a function to communicate to its top-level funcDecl that it should
	// include a defer prelude+prologue.
	usesDefer bool

	globalVars     []*ast.Ident
	functions      []*ast.FuncDecl
	namedTypeSpecs []*ast.TypeSpec

	importNames        map[string]*types.PkgName
	importNamesOrdered []*types.PkgName

	inits []glang.Expr

	filter declfilter.DeclFilter
	out    outputDecls
}

// NewPkgCtx initializes a context based on a properly loaded package
func NewPkgCtx(pkg *packages.Package, filter declfilter.DeclFilter) Ctx {
	declImplicitParams := ""
	if util.GetFfi(pkg) == "" {
		declImplicitParams = " {ext : ffi_syntax}"
	}
	return Ctx{
		info:               pkg.TypesInfo,
		pkgPath:            pkg.PkgPath,
		declImplicitParams: declImplicitParams,
		pkgIdent:           "pkg_id" + "." + pkg.Name,
		errorReporter:      newErrorReporter(pkg.Fset),
		importNames:        make(map[string]*types.PkgName),
		filter:             filter,
	}
}

func (ctx *Ctx) paramList(fs *ast.FieldList) (names []glang.Binder, types []glang.Expr) {
	for _, f := range fs.List {
		for _, name := range f.Names {
			names = append(names, glang.Binder{
				Name: name.Name,
			})
			types = append(types, ctx.glangType(f, ctx.typeOf(f.Type)))
		}
		if len(f.Names) == 0 { // Unnamed parameter
			names = append(names, glang.Binder{
				Name: "_",
			})
			types = append(types, ctx.glangType(f, ctx.typeOf(f.Type)))
		}
	}
	return names, types
}

func (ctx *Ctx) gallinaIdent(x string) glang.Expr {
	return glang.GallinaIdent(x)
}

func (ctx *Ctx) typeParamList(fs *ast.FieldList) []string {
	var typeParams []string
	if fs == nil {
		return nil
	}
	for _, f := range fs.List {
		for _, name := range f.Names {
			typeParams = append(typeParams, name.Name)
		}

		if len(f.Names) == 0 { // Unnamed parameter
			ctx.unsupported(fs, "unnamed type parameters")
		}
	}
	return typeParams
}

func addSourceDoc(doc *ast.CommentGroup, comment *string) {
	if doc == nil {
		return
	}
	if *comment != "" {
		*comment += "\n\n"
	}
	*comment += strings.TrimSuffix(doc.Text(), "\n")
}

func (ctx *Ctx) addSourceFile(d *ast.FuncDecl, comment *string) {
	if *comment != "" {
		*comment += "\n\n"
	}
	f := ctx.fset.Position(d.Name.Pos())
	f.Filename = filepath.Base(f.Filename)
	*comment += "go: " + f.String()
}

// TODO: make this the input to handleImplicitConversion?
type exprWithInfo struct {
	e glang.Expr
	t types.Type // for conversions
	n ast.Node   // for printing a location in error messages
}

func (ctx *Ctx) sliceLiteralAux(es []exprWithInfo, expectedType types.Type) glang.Expr {
	var expr glang.Expr = glang.VerbatimExpr("#slice.nil")

	if len(es) > 0 {
		var sliceLitArgs []glang.Expr
		for i := 0; i < len(es); i++ {
			sliceLitArgs = append(sliceLitArgs,
				glang.NewCallExpr(
					glang.VerbatimExpr("KeyedElement"),
					glang.VerbatimExpr("None"),
					glang.NewCallExpr(
						glang.VerbatimExpr("ElementExpression"),
						ctx.glangType(es[i].n, expectedType),
						glang.IdentExpr(fmt.Sprintf("$sl%d", i))),
				),
			)
		}
		expr = glang.NewCallExpr(glang.VerbatimExpr("CompositeLiteral"),
			ctx.glangType(es[0].n, types.NewSlice(expectedType)),
			glang.NewCallExpr(glang.VerbatimExpr("LiteralValue"), glang.ListExpr(sliceLitArgs)),
		)

		for i := len(es); i > 0; i-- {
			expr = glang.LetExpr{
				Names:   []string{fmt.Sprintf("$sl%d", i-1)},
				ValExpr: ctx.handleImplicitConversion(es[i-1].n, es[i-1].t, expectedType, es[i-1].e),
				Cont:    expr,
			}
		}
		expr = glang.ParenExpr{Inner: expr}
	}
	return expr
}

// Deals with the arguments, but does not actually invoke the function. That
// should be done in the continuation. The continuation can assume the arguments
// are bound to "a0", "$a1", ....
func (ctx *Ctx) callExprPrelude(call *ast.CallExpr, cont glang.Expr) (expr glang.Expr) {
	funcSig, ok := ctx.typeOf(call.Fun).Underlying().(*types.Signature)
	if !ok {
		ctx.nope(call.Fun, "function should have signature type, got %T", types.Unalias(ctx.typeOf(call.Fun)))
	}

	expr = cont

	var intermediates []exprWithInfo
	intermediatesDone := false
	// look for special case of multi-return pass through
	if len(call.Args) == 1 {
		if tupleType, ok := ctx.typeOf(call.Args[0]).(*types.Tuple); ok {
			intermediatesDone = true
			for i := range tupleType.Len() {
				intermediates = append(intermediates,
					exprWithInfo{
						e: glang.IdentExpr(fmt.Sprintf("$ret%d", i)),
						t: tupleType.At(i).Type(),
						n: call.Args[0],
					})
			}
			// destructure the inner call at the end
			defer func() {
				var names []string
				for i := range tupleType.Len() {
					names = append(names, fmt.Sprintf("$ret%d", i))
				}
				expr = glang.LetExpr{
					Names:   names,
					ValExpr: glang.ParenExpr{Inner: ctx.expr(call.Args[0])},
					Cont:    expr,
				}
			}()
		}
	}
	if !intermediatesDone {
		for i := range len(call.Args) {
			intermediates = append(intermediates,
				exprWithInfo{
					e: ctx.expr(call.Args[i]),
					t: ctx.typeOf(call.Args[i]),
					n: call.Args[i],
				})
		}
	}

	var i int = funcSig.Params().Len()
	if funcSig.Variadic() && call.Ellipsis == token.NoPos {
		// construct a slice literal for all the arguments including and after
		// the last one listed in funcSig.
		expr = glang.LetExpr{
			Names: []string{fmt.Sprintf("$a%d", i-1)},
			ValExpr: ctx.sliceLiteralAux(intermediates[i-1:],
				funcSig.Params().At(i-1).Type().(*types.Slice).Elem()),
			Cont: expr,
		}
		i--
	}
	for ; i > 0; i-- {
		expr = glang.LetExpr{
			Names: []string{fmt.Sprintf("$a%d", i-1)},
			ValExpr: ctx.handleImplicitConversion(intermediates[i-1].n,
				intermediates[i-1].t, funcSig.Params().At(i-1).Type(), intermediates[i-1].e),
			Cont: expr,
		}
	}
	return
}

func (ctx *Ctx) conversionExpr(s *ast.CallExpr) glang.Expr {
	if len(s.Args) != 1 {
		ctx.nope(s, "expect exactly one argument in a conversion")
	}
	toType := ctx.info.TypeOf(s.Fun)
	fromType := ctx.info.TypeOf(s.Args[0])
	return ctx.handleImplicitConversion(s, fromType, toType, ctx.expr(s.Args[0]))
}

// This handles:
// - make() and new() because they uniquely take a type as a normal parameter.
// - array len() and cap() because they are untyped functions
func (ctx *Ctx) maybeHandleSpecialBuiltin(s *ast.CallExpr) (glang.Expr, bool) {
	if !ctx.info.Types[s.Fun].IsBuiltin() {
		return nil, false
	}

	f, ok := s.Fun.(*ast.Ident)
	if !ok {
		ctx.unsupported(s.Fun, "builtin that isn't an ident")
	}

	switch f.Name {
	case "make":
		sig := ctx.typeOf(s.Fun).(*types.Signature)
		ty := ctx.glangType(s.Fun, sig.Params().At(0).Type())
		switch sig.Params().Len() {
		case 1:
			return glang.NewCallExpr(
				glang.NewCallExpr(glang.VerbatimExpr("FuncResolve"),
					glang.VerbatimExpr("go.make1"), glang.ListExpr{ty}, glang.Tt),
				glang.Tt), true
		case 2:
			return glang.NewCallExpr(
				glang.NewCallExpr(glang.VerbatimExpr("FuncResolve"),
					glang.VerbatimExpr("go.make2"), glang.ListExpr{ty}, glang.Tt),
				ctx.expr(s.Args[1])), true
		case 3:
			return glang.NewCallExpr(
				glang.NewCallExpr(glang.VerbatimExpr("FuncResolve"),
					glang.VerbatimExpr("go.make3"), glang.ListExpr{ty}, glang.Tt),
				ctx.expr(s.Args[1]), ctx.expr(s.Args[2])), true
		default:
			ctx.nope(s, "Too many or too few arguments to make")
			return glang.CallExpr{}, true
		}
	case "new":
		tv := ctx.info.Types[s.Args[0]]
		var ty glang.Expr
		var e glang.Expr
		if tv.IsType() {
			ty = ctx.glangType(s.Args[0], tv.Type)
			e = glang.NewCallExpr(glang.VerbatimExpr("GoZeroVal"), ty, glang.Tt)
		} else {
			ty = ctx.glangType(s.Args[0], ctx.typeOf(s.Args[0]))
			e = ctx.expr(s.Args[0])
		}
		return glang.NewCallExpr(glang.VerbatimExpr("GoAlloc"), ty, e), true
	case "len", "cap":
		if _, ok := ctx.typeOf(s.Fun).(*types.Signature); ok {
			return nil, false
		}
		name := s.Fun.(*ast.Ident).Name
		return glang.NewCallExpr(glang.VerbatimExpr("FuncResolve"),
			glang.VerbatimExpr("go."+name), glang.ListExpr{ctx.glangType(s, ctx.typeOf(s.Args[0]))},
			glang.Tt), true
	}

	return nil, false
}

func (ctx *Ctx) getNumParams(e ast.Expr) int {
	funcSig, ok := ctx.typeOf(e).Underlying().(*types.Signature)
	if !ok {
		ctx.nope(e, "function should have signature type, got %T", types.Unalias(ctx.typeOf(e)))
	}
	return funcSig.Params().Len()
}

func (ctx *Ctx) callExpr(s *ast.CallExpr) glang.Expr {
	if ctx.info.Types[s.Fun].IsType() {
		return ctx.conversionExpr(s)
	} else if e, ok := ctx.maybeHandleSpecialBuiltin(s); ok {
		return e
	} else {
		var args []glang.Expr
		for i := range ctx.getNumParams(s.Fun) {
			args = append(args, glang.IdentExpr(fmt.Sprintf("$a%d", i)))
		}
		return ctx.callExprPrelude(s, glang.NewCallExpr(ctx.expr(s.Fun), args...))
	}
}

func (ctx *Ctx) qualifiedName(obj types.Object) string {
	name := obj.Name()
	if obj.Pkg() == nil {
		return name
	} else if ctx.pkgPath == obj.Pkg().Path() {
		// no module name needed
		return name
	}
	return fmt.Sprintf("%s.%s", obj.Pkg().Name(), name)
}

func (ctx *Ctx) selectorExprAddr(e *ast.SelectorExpr) glang.Expr {
	selection := ctx.info.Selections[e]
	if selection == nil {
		if v, ok := ctx.info.ObjectOf(e.Sel).(*types.Var); ok {
			return glang.NewCallExpr(glang.VerbatimExpr("GlobalVarAddr"),
				ctx.gallinaIdent(v.Pkg().Name()+"."+v.Name()),
				glang.Tt,
			)
		} else {
			ctx.unsupported(e, "address of external package selection that is not a variable")
		}
	}

	switch selection.Kind() {
	case types.FieldVal:
		if ctx.info.Types[e.X].Addressable() {
			expr, curType, index := ctx.exprAddr(e.X), selection.Recv(), selection.Index()
			ctx.fieldAddrSelection(e, index, &curType, &expr)
			return expr
		} else {
			expr, curType, index := ctx.expr(e.X), selection.Recv(), selection.Index()
			ctx.fieldSelection(e.X, &index, &curType, &expr)
			if len(index) == 0 {
				ctx.nope(e, "expected addressable expression")
			}
			ctx.fieldAddrSelection(e.X, index, &curType, &expr)
			return expr
		}
	case types.MethodVal:
		ctx.nope(e, "method val is not addressable")
	case types.MethodExpr:
		ctx.nope(e, "method expr is not addressable")
	}
	ctx.nope(e, "unexpected kind of selection")
	panic("unreachable")
}

// Requires that `old(expr) : old(curType)` and that `old(curType)` be a struct
// type. This walks down the selection specified by `index` up until it sees a
// pointer field, then returns. Its intent is to be combined with
// fieldAddrSelection to go the rest of the way.
//
// If len(index) > 0, then `expr : ptr<curType>`.
// If len(index) == 0, then `expr : curType`.
func (ctx *Ctx) fieldSelection(n locatable, index *[]int, curType *types.Type, expr *glang.Expr) {
	for ; len(*index) > 0; *index = (*index)[1:] {
		i := (*index)[0]
		info, ok := ctx.getStructInfo(*curType)
		if !ok {
			ctx.nope(n, "expected (pointer to) struct type for base of selector, got %s", *curType)
		}

		if info.throughPointer {
			// XXX: this is to feed into fieldAddrSelection (see comment above this func).
			*curType = (*curType).(*types.Pointer).Elem()
			return
		}
		v := info.structType.Field(i)
		*expr = glang.NewCallExpr(glang.VerbatimExpr("StructFieldGet"),
			ctx.structInfoToGlangType(info), glang.GallinaString(v.Name()), *expr)
		*curType = v.Type()
	}
}

// Requires `old(expr) : ptr<old(curType)>`.
// This walks down the selection specified by `index` all the way to the end,
// returning an expression representing the address of that selected field.
func (ctx *Ctx) fieldAddrSelection(n locatable, index []int, curType *types.Type, expr *glang.Expr) {
	for _, i := range index {
		info, ok := ctx.getStructInfo(*curType)
		if !ok {
			if _, ok := (*curType).(*types.Struct); ok {
				ctx.unsupported(n, "anonymous struct")
			}
			ctx.nope(n, "expected (pointer to) struct type for base of selector, got %s", *curType)
		}
		if info.throughPointer {
			*expr = glang.DerefExpr{X: *expr, Ty: ctx.glangType(n, *curType)}
		}
		v := info.structType.Field(i)

		*expr = glang.NewCallExpr(glang.VerbatimExpr("StructFieldRef"),
			ctx.glangType(n, info.namedType), glang.StringLiteral{Value: v.Name()}, *expr)
		*curType = v.Type()
	}
}

func (ctx *Ctx) selectorExpr(e *ast.SelectorExpr) glang.Expr {
	selection := ctx.info.Selections[e]
	if selection == nil {
		if _, ok := ctx.info.ObjectOf(e.Sel).(*types.Var); ok {
			ctx.nope(e, "global variable from external package should be handled by exprAddr")
		} else if f, ok := ctx.info.ObjectOf(e.Sel).(*types.Func); ok {
			// package-qualified function
			typeArgs := ctx.info.Instances[e.Sel].TypeArgs
			args := glang.ListExpr(ctx.convertTypeArgsToGlang(nil, typeArgs))
			return glang.NewCallExpr(
				glang.VerbatimExpr("FuncResolve"),
				ctx.gallinaIdent(f.Pkg().Name()+"."+f.Name()),
				args,
				glang.Tt,
			)
		} else {
			return ctx.handleImplicitConversion(e,
				ctx.info.TypeOf(e.Sel),
				ctx.info.TypeOf(e),
				glang.PackageIdent{
					Package: ctx.info.ObjectOf(e.Sel).Pkg().Name(),
					Ident:   e.Sel.Name,
				},
			)
		}
	}

	switch selection.Kind() {
	case types.MethodExpr:
		ctx.unsupported(e, "method expr")
	case types.FieldVal:
		var expr glang.Expr
		index, curType := selection.Index(), selection.Recv()

		if ctx.info.Types[e.X].Addressable() {
			expr = ctx.exprAddr(e.X)
		} else {
			expr = ctx.expr(e.X)
			ctx.fieldSelection(e.X, &index, &curType, &expr)
		}
		if len(index) > 0 {
			ctx.fieldAddrSelection(e.X, index, &curType, &expr)
			expr = glang.DerefExpr{X: expr, Ty: ctx.glangType(e.Sel, curType)}
		}
		return expr

	case types.MethodVal:
		// 2*2 cases: receiver type could be (T) or (*T), and e.X type
		// (including embedded fields) could be (T) or (*T).

		f := selection.Obj().(*types.Func)
		receiverType := types.Unalias(ctx.typeOf(e.X))
		receiver := ctx.expr(e.X)
		methodExpr := glang.StringLiteral{Value: e.Sel.Name}

		// If x is addressable and &x's method set contains m, x.m() is shorthand for (&x).m().
		if ctx.info.Types[e.X].Addressable() {
			ptrType := types.NewPointer(receiverType)
			if obj, _, _ := types.LookupFieldOrMethod(ptrType, false, f.Pkg(), f.Name()); obj != nil {
				receiverType = ptrType
				receiver = ctx.exprAddr(e.X)
			}
		}
		typeExpr := ctx.glangType(e.X, receiverType)

		return glang.NewCallExpr(glang.VerbatimExpr("MethodResolve"), typeExpr, methodExpr, receiver)
	}
	panic("unreachable")
}

type compositeBinding struct {
	name string
	val  glang.Expr
}

func (ctx *Ctx) compositeLiteral(e *ast.CompositeLit) glang.Expr {
	var bindings []compositeBinding
	res := ctx.compositeLiteralWithBindings(e, &bindings)

	for i := len(bindings) - 1; i >= 0; i-- {
		res = glang.LetExpr{
			Names:   []string{bindings[i].name},
			ValExpr: bindings[i].val,
			Cont:    res,
		}
	}
	return res
}

func (ctx *Ctx) compositeLiteralWithBindings(e *ast.CompositeLit, bindings *[]compositeBinding) glang.Expr {
	var elements glang.ListExpr

	handleValue := func(ev ast.Expr) glang.Expr {
		switch ev := ev.(type) {
		case *ast.CompositeLit:
			if ev.Type == nil {
				return ctx.compositeLiteralWithBindings(ev, bindings)
			}
		}

		name := fmt.Sprintf("$v%d", len(*bindings))
		*bindings = append(*bindings, compositeBinding{name: name, val: ctx.expr(ev)})
		return glang.NewCallExpr(glang.VerbatimExpr("ElementExpression"),
			ctx.glangType(ev, ctx.typeOf(ev)), glang.IdentExpr(name))
	}

	for _, el := range e.Elts {
		var k glang.Expr = glang.VerbatimExpr("None")
		var v glang.Expr

		switch el := el.(type) {
		case *ast.KeyValueExpr:
			done := false
			if elKey, ok := el.Key.(*ast.Ident); ok {
				if vr, ok := ctx.info.Uses[elKey].(*types.Var); ok && vr.Kind() == types.FieldVar {
					k = glang.NewCallExpr(glang.VerbatimExpr("KeyField"),
						glang.StringLiteral{Value: elKey.Name})
					done = true
				}
			}
			if !done {
				name := fmt.Sprintf("$k%d", len(*bindings))
				*bindings = append(*bindings, compositeBinding{name: name, val: ctx.expr(el.Key)})
				k = glang.NewCallExpr(glang.VerbatimExpr("KeyExpression"),
					ctx.glangType(el.Key, ctx.typeOf(el.Key)), glang.IdentExpr(name))
			}
			k = glang.NewCallExpr(glang.VerbatimExpr("Some"), k)
			v = handleValue(el.Value)
		default:
			v = handleValue(el)
		}

		elements = append(elements, glang.NewCallExpr(glang.VerbatimExpr("KeyedElement"), k, v))
	}

	if e.Type != nil {
		return glang.NewCallExpr(glang.VerbatimExpr("CompositeLiteral"),
			ctx.glangType(e.Type, ctx.typeOf(e.Type)),
			glang.NewCallExpr(glang.VerbatimExpr("LiteralValue"), elements))
	} else {
		return glang.NewCallExpr(glang.VerbatimExpr("ElementLiteralValue"), elements)
	}
}

func (ctx *Ctx) basicLiteral(e *ast.BasicLit) glang.Expr {
	return ctx.constantLiteral(e)
}

func (ctx *Ctx) typeJoin(n ast.Node, t1, t2 types.Type) types.Type {
	if types.AssignableTo(t1, t2) {
		return t2
	} else if types.AssignableTo(t2, t1) {
		return t1
	} else {
		ctx.unsupported(n, "comparison between non-assignable types")
		return nil
	}
}

var shiftOps = map[token.Token]struct{}{
	token.SHL: {},
	token.SHR: {},
}

func (ctx *Ctx) binExpr(e *ast.BinaryExpr) (expr glang.Expr) {
	// XXX: according to the Go spec, comparisons can occur between types that
	// are "assignable" to one another. This may require a conversion, so we
	// here convert to the appropriate type here.
	//
	// This also handles converting untyped constants to a typed constant.
	xT, yT := ctx.typeOf(e.X), ctx.typeOf(e.Y)
	var compType types.Type
	if _, ok := shiftOps[e.Op]; ok {
		// Shifts should be converted to the type of the base; the shift amount and
		// the base do not need to have a type join (e.g., x << y where x is a uint8
		// and y is a uint32)
		compType = xT
	} else {
		compType = ctx.typeJoin(e, xT, yT)
	}

	op := gooseLangOps[e.Op]

	if t, ok := compType.(*types.Basic); ok {
		switch t.Kind() {
		case types.UntypedInt, types.UntypedString:
			return ctx.constantLiteral(e)
		}
	}
	expr = glang.BinaryExpr{
		X: ctx.handleImplicitConversion(e.X, xT, compType, ctx.expr(e.X)),
		Op: glang.BinOp{
			OpId: op,
			Type: ctx.glangType(e, compType),
		},
		Y: ctx.handleImplicitConversion(e.Y, yT, compType, ctx.expr(e.Y)),
	}

	// FIXME: might need to do a conversion here. Handle e.g. interface
	// conversion of (x < 10) as well as conversion of (x + 10).
	// expr = ctx.handleImplicitConversion(e, compType, ctx.typeOf(e), expr)
	return expr
}

func (ctx *Ctx) sliceExpr(e *ast.SliceExpr) glang.Expr {
	ty := ctx.glangType(e, ctx.typeOf(e.X))
	var lowExpr glang.Expr = glang.Int64Val{Value: glang.IntToZ(0)}
	var highExpr glang.Expr = glang.NewCallExpr(
		glang.VerbatimExpr("FuncResolve"),
		glang.VerbatimExpr("go.len"), glang.ListExpr{ty}, glang.Tt, ctx.expr(e.X))
	x := ctx.expr(e.X)

	if e.Low != nil {
		lowExpr = ctx.expr(e.Low)
	}
	if e.High != nil {
		highExpr = ctx.expr(e.High)
	}
	if e.Max != nil {
		highExpr = ctx.expr(e.High)
		return glang.LetExpr{
			Names:   []string{"$s"},
			ValExpr: x,
			Cont: glang.NewCallExpr(glang.VerbatimExpr("FullSlice"), ty,
				glang.TupleExpr{glang.IdentExpr("$s"), lowExpr, highExpr, ctx.expr(e.Max)}),
		}
	} else {
		return glang.LetExpr{
			Names:   []string{"$s"},
			ValExpr: x,
			Cont: glang.NewCallExpr(glang.VerbatimExpr("Slice"), ty,
				glang.TupleExpr{glang.IdentExpr("$s"), lowExpr, highExpr}),
		}
	}
}

func (ctx *Ctx) unaryExpr(e *ast.UnaryExpr, multipleBindings bool) glang.Expr {
	if e.Op == token.NOT {
		return glang.NotExpr{X: ctx.expr(e.X)}
	}
	if e.Op == token.XOR {
		return glang.NotExpr{X: ctx.expr(e.X)}
	}
	if e.Op == token.AND {
		if cl, ok := e.X.(*ast.CompositeLit); ok {
			// e is &T{...} (a composite literal)
			sl := ctx.compositeLiteral(cl)
			return glang.NewCallExpr(glang.VerbatimExpr("GoAlloc"),
				ctx.glangType(cl.Type, ctx.typeOf(e.X)), sl)
		}
		// e is something else
		return ctx.exprAddr(e.X)
	}
	if e.Op == token.ARROW {
		var expr glang.Expr = glang.NewCallExpr(glang.VerbatimExpr("chan.receive"),
			ctx.glangType(e, chanElem(ctx.typeOf(e.X))),
			ctx.expr(e.X))
		if !multipleBindings {
			expr = glang.NewCallExpr(glang.VerbatimExpr("Fst"), expr)
		}
		return expr
	}
	op, ok := gooseLangOps[e.Op]
	if !ok {
		ctx.unsupported(e, "unary expression %s", e.Op)
	}
	ty := ctx.typeOf(e.X)
	expr := glang.UnaryExpr{
		X: ctx.expr(e.X),
		Op: glang.UnaryOp{
			OpId: op,
			Type: ctx.glangType(e.X, ty),
		},
	}
	return ctx.handleImplicitConversion(e, ty, ctx.typeOf(e), expr)
}

func (ctx *Ctx) function(s *ast.Ident) glang.Expr {
	if ctx.info.ObjectOf(s).Pkg().Path() != ctx.pkgPath {
		ctx.nope(s, "expected function ident to refer to local function")
	}
	f, ok := ctx.info.ObjectOf(s).(*types.Func)
	if !ok {
		ctx.nope(s, "expected to get a types.Func object for function ident")
	}
	typeArgs := ctx.info.Instances[s].TypeArgs
	return glang.NewCallExpr(glang.VerbatimExpr("FuncResolve"),
		ctx.gallinaIdent(f.Name()),
		glang.ListExpr(ctx.convertTypeArgsToGlang(s, typeArgs)),
		glang.Tt,
	)
}

func (ctx *Ctx) goBuiltin(e *ast.Ident) bool {
	s, ok := ctx.info.Uses[e]
	if !ok {
		return false
	}
	return s.Parent() == types.Universe
}

// if types.Type is an interface that holds a single type, get that type; these
// typically show up as constraints in generic functions, e.g. `T ~[]int`
func getInterfaceSingletonType(t types.Type) (types.Type, bool) {
	if t, ok := t.Underlying().(*types.Interface); ok {
		if t.NumEmbeddeds() == 1 {
			t := t.EmbeddedType(0)
			if t, ok := t.(*types.Union); ok {
				if t.Len() == 1 {
					// singleton union (possibly with term.Tilde() being true)
					term := t.Term(0)
					// the single type in the union is unionT
					unionT := term.Type()
					return unionT, true
				}
			}
		}
	}
	return nil, false
}

// underlyingType returns the underlying type of t, including if t is of an
// singleton interface.
func underlyingType(t types.Type) types.Type {
	if t, ok := getInterfaceSingletonType(t); ok {
		return t.Underlying()
	}
	return t.Underlying()
}

func (ctx *Ctx) builtinIdent(e *ast.Ident) glang.Expr {
	switch e.Name {
	case "nil":
		return glang.VerbatimExpr("UntypedNil")
	case "true":
		return glang.GooseBoolLiteral(true)
	case "false":
		return glang.GooseBoolLiteral(false)
	case "append", "len", "cap", "copy", "delete", "close", "clear":
		sig := ctx.typeOf(e).(*types.Signature)
		ty := ctx.glangType(e, sig.Params().At(0).Type())
		return glang.NewCallExpr(glang.VerbatimExpr("FuncResolve"),
			glang.VerbatimExpr("go."+e.Name), glang.ListExpr{ty}, glang.Tt)
	case "new":
		ctx.nope(e, "new should be handled elsewhere")
	case "panic":
		return glang.NewCallExpr(glang.VerbatimExpr("FuncResolve"),
			glang.VerbatimExpr("go."+e.Name), glang.ListExpr{}, glang.Tt)

	case "min", "max":
		sig := ctx.typeOf(e).(*types.Signature)
		if sig.Params().Len() == 0 {
			ctx.nope(e, "min/max with no params")
		}
		// figure out the desired type by taking a type join of everything.
		// XXX: the signature might always be (T, T, T, T, T).
		var t types.Type = sig.Params().At(0).Type().Underlying()
		for i := 0; i < sig.Params().Len(); i++ {
			t = ctx.typeJoin(e, t, sig.Params().At(i).Type())
		}
		var typeArgs glang.ListExpr
		ty := ctx.glangType(e, t)
		for i := 0; i < sig.Params().Len(); i++ {
			typeArgs = append(typeArgs, ty)
		}

		return glang.NewCallExpr(glang.VerbatimExpr("FuncResolve"),
			glang.VerbatimExpr("go."+e.Name), typeArgs, glang.Tt)
	case "iota":
		return ctx.constantLiteral(e)
	case "recover":
		return glang.NewCallExpr(glang.VerbatimExpr("FuncResolve"),
			glang.VerbatimExpr("go."+e.Name), glang.ListExpr{}, glang.Tt)
	default:
		ctx.unsupported(e, "builtin identifier of type %v", ctx.typeOf(e))
	}
	return nil
}

// untypedFloatToInt converts a constant (assumed to be a float) to an integer.
//
// Returns ok = false if the float doesn't fit in an int64.
func untypedFloatToInt(c constant.Value) (i int64, ok bool) {
	switch x := constant.Val(c).(type) {
	case *big.Rat:
		if x.IsInt() {
			v, exact := x.Float64()
			if !exact {
				return 0, false
			}
			return int64(v), true
		}
	case *big.Float:
		if x.IsInt() {
			var acc big.Accuracy
			i, acc = x.Int64()
			if acc != big.Exact {
				return 0, false
			}
			return i, true
		}
	}
	return 0, false
}

func (ctx *Ctx) identExpr(e *ast.Ident, multipleBindings bool) glang.Expr {
	// XXX: special case for a manually constructed Ident from select recv clause
	if len(e.Name) > 0 && e.Name[0] == '$' {
		var expr glang.Expr = glang.IdentExpr(e.Name)
		if !multipleBindings {
			expr = glang.NewCallExpr(glang.VerbatimExpr("Fst"), expr)
		}
		return expr
	}

	if ctx.goBuiltin(e) {
		return ctx.builtinIdent(e)
	}

	// check if e refers to a variable,
	obj := ctx.info.ObjectOf(e)
	if constObj, ok := obj.(*types.Const); ok {
		// is a constant
		if constTy, ok := constObj.Type().(*types.Basic); ok && constTy.Kind() == types.UntypedFloat {
			dstTy := ctx.typeOf(e)
			if dstTy, ok := dstTy.(*types.Basic); ok && dstTy.Info()&types.IsInteger != 0 {
				constInt, exact := untypedFloatToInt(constObj.Val())
				if !exact {
					ctx.nope(e, "float constant does not fit into int64")
				}
				constExpr := glang.VerbatimExpr(fmt.Sprintf("%d", constInt))
				switch dstTy.Kind() {
				case types.Uint64, types.Int64, types.Int:
					return glang.Int64Val{
						Value: constExpr,
					}
				case types.Uint32, types.Int32:
					return glang.Int32Val{
						Value: constExpr,
					}
				case types.Uint16, types.Int16:
					return glang.Int16Val{
						Value: constExpr,
					}
				case types.Uint8, types.Int8:
					return glang.Int8Val{
						Value: constExpr,
					}
				}
			}
		}
		constE := ctx.gallinaIdent(e.Name)
		return ctx.handleImplicitConversion(e, constObj.Type(), ctx.typeOf(e), constE)
	}
	if _, ok := obj.(*types.Var); ok {
		ctx.nope(e, "variable references should get translated via exprAddr")
	}
	if _, ok := obj.(*types.Func); ok {
		// is a function
		return ctx.function(e)
	}
	ctx.unsupported(e, "unrecognized kind of identifier; not local variable or global function")
	panic("")
}

func (ctx *Ctx) indexExpr(e *ast.IndexExpr, multipleBindings bool) glang.Expr {
	xTy := ctx.typeOf(e.X).Underlying()
	switch xTy := xTy.(type) {
	case *types.Map:
		if multipleBindings {
			return glang.NewCallExpr(glang.VerbatimExpr("map.lookup2"),
				ctx.glangType(e.X, xTy.Key()),
				ctx.glangType(e.X, xTy.Elem()),
				ctx.expr(e.X),
				ctx.exprIntoType(e.Index, xTy.Key()))
		} else {
			return glang.NewCallExpr(glang.VerbatimExpr("map.lookup1"),
				ctx.glangType(e.X, xTy.Key()),
				ctx.glangType(e.X, xTy.Elem()),
				ctx.expr(e.X),
				ctx.exprIntoType(e.Index, xTy.Key()))
		}
	case *types.Signature:
		// generic arguments are grabbed from go ast, ignore explicit type args
		return ctx.expr(e.X)
	}

	return glang.NewCallExpr(glang.VerbatimExpr("Index"),
		ctx.glangType(e, ctx.typeOf(e.X)),
		glang.TupleExpr{ctx.expr(e.X),
			ctx.exprIntoType(e.Index, types.Typ[types.Int])})
}

func (ctx *Ctx) indexListExpr(e *ast.IndexListExpr) glang.Expr {
	// generic arguments are grabbed from go ast, ignore explicit type args
	return ctx.expr(e.X)
}

func (ctx *Ctx) derefExpr(e ast.Expr) glang.Expr {
	return glang.DerefExpr{
		X:  ctx.expr(e),
		Ty: ctx.glangType(e, ptrElem(ctx.typeOf(e))),
	}
}

func (ctx *Ctx) expr(e ast.Expr) glang.Expr {
	if ctx.info.Types[e].Addressable() {
		return glang.DerefExpr{X: ctx.exprAddr(e), Ty: ctx.glangType(e, ctx.typeOf(e))}
	} else {
		return ctx.exprSpecial(e, false)
	}
}

func (ctx *Ctx) funcLit(e *ast.FuncLit) glang.FuncLit {
	fl := glang.FuncLit{}

	// reset to original value after translating this FuncLit
	defer func(b bool) {
		ctx.usesDefer = b
	}(ctx.usesDefer)
	defer func(defaultReturn glang.Expr) {
		ctx.defaultReturn = defaultReturn
	}(ctx.defaultReturn)

	ctx.usesDefer = false

	// Assemble the `defaultReturn` expr so the body's `return` statements can use it.
	var defaultRetExpr glang.TupleExpr
	if e.Type.Results == nil || len(e.Type.Results.List) == 0 {
		defaultRetExpr = append(defaultRetExpr, glang.Tt)
	} else {
		for _, r := range e.Type.Results.List {
			if r.Names == nil {

			} else {
				for _, name := range r.Names {
					defaultRetExpr = append(defaultRetExpr,
						glang.DerefExpr{
							X:  glang.IdentExpr(name.Name),
							Ty: ctx.glangType(r.Type, ctx.typeOf(r.Type)),
						})
				}
			}
		}
	}
	ctx.defaultReturn = glang.ReturnExpr{
		Value: defaultRetExpr,
	}

	defer func(oldFuncType *types.Signature) {
		ctx.curFuncType = oldFuncType
	}(ctx.curFuncType)

	ctx.curFuncType = ctx.typeOf(e.Type).(*types.Signature)
	var argTypes []glang.Expr
	fl.Args, argTypes = ctx.paramList(e.Type.Params)
	var cont glang.Expr = nil
	if e.Type.Results == nil {
		// explicitly return #() at end of void functions
		cont = glang.ReturnExpr{Value: glang.Tt}
	}
	fl.Body = ctx.blockStmt(e.Body, cont)

	// Create heap-allocated variables for all of the function parameters
	for i, arg := range fl.Args {
		// skip anonymous parameters (which can't be used)
		if arg.Name != "_" && arg.Name != "" {
			fl.Body = glang.LetExpr{
				Names: []string{arg.Name},
				ValExpr: glang.NewCallExpr(
					glang.VerbatimExpr("GoAlloc"),
					argTypes[i], glang.IdentExpr(arg.Name)),
				Cont: fl.Body,
			}
		}
	}
	if e.Type.Results != nil {
		for _, r := range e.Type.Results.List {
			t := ctx.glangType(r.Type, ctx.typeOf(r.Type))
			for _, name := range r.Names {
				fl.Body = glang.LetExpr{
					Names: []string{name.Name},
					ValExpr: glang.NewCallExpr(glang.VerbatimExpr("GoAlloc"), t,
						glang.NewCallExpr(glang.VerbatimExpr("GoZeroVal"), t, glang.Tt)),
					Cont: fl.Body,
				}
			}
		}
	}

	if ctx.usesDefer {
		fl.Body = glang.NewCallExpr(glang.VerbatimExpr("with_defer:"), fl.Body)
	} else {
		fl.Body = glang.NewCallExpr(glang.VerbatimExpr("exception_do"), fl.Body)
	}

	return fl
}

func (ctx *Ctx) typeAssertExpr(e *ast.TypeAssertExpr, multipleBindings bool) glang.Expr {
	ty := ctx.glangType(e, ctx.typeOf(e.Type))
	if multipleBindings {
		return glang.NewCallExpr(glang.VerbatimExpr("TypeAssert2"),
			ty,
			ctx.expr(e.X),
		)
	}
	return glang.NewCallExpr(glang.VerbatimExpr("TypeAssert"), ty, ctx.expr(e.X))
}

func (ctx *Ctx) exprSpecial(e ast.Expr, multipleBindings bool) glang.Expr {
	switch e := e.(type) {
	case *ast.CallExpr:
		return ctx.callExpr(e)
	case *ast.Ident:
		return ctx.identExpr(e, multipleBindings)
	case *ast.SelectorExpr:
		return ctx.selectorExpr(e)
	case *ast.CompositeLit:
		return ctx.compositeLiteral(e)
	case *ast.BasicLit:
		return ctx.basicLiteral(e)
	case *ast.BinaryExpr:
		return ctx.binExpr(e)
	case *ast.SliceExpr:
		return ctx.sliceExpr(e)
	case *ast.IndexExpr:
		return ctx.indexExpr(e, multipleBindings)
	case *ast.IndexListExpr:
		return ctx.indexListExpr(e)
	case *ast.UnaryExpr:
		return ctx.unaryExpr(e, multipleBindings)
	case *ast.ParenExpr:
		return ctx.expr(e.X)
	case *ast.StarExpr:
		return ctx.derefExpr(e.X)
	case *ast.TypeAssertExpr:
		return ctx.typeAssertExpr(e, multipleBindings)
	case *ast.FuncLit:
		return ctx.funcLit(e)
	default:
		ctx.unsupported(e, "unexpected expr")
	}
	return nil
}

func (ctx *Ctx) stmtList(ss []ast.Stmt, cont glang.Expr) glang.Expr {
	if len(ss) == 0 {
		return glang.DoExpr{Expr: glang.Tt}
	}
	var e glang.Expr = nil
	for len(ss) > 0 {
		stmt := ss[len(ss)-1]
		ss = ss[:len(ss)-1]
		e = ctx.stmt(stmt, e)
	}
	return glang.SeqExpr{Expr: e, Cont: cont}
}

func (ctx *Ctx) blockStmt(s *ast.BlockStmt, cont glang.Expr) glang.Expr {
	return ctx.stmtList(s.List, cont)
}

func (ctx *Ctx) switchStmt(s *ast.SwitchStmt, cont glang.Expr) (e glang.Expr) {
	var tagExpr glang.Expr = glang.GooseBoolLiteral(true)

	var tagType types.Type = types.Typ[types.Bool]

	if s.Tag != nil {
		tagType = ctx.typeOf(s.Tag)
		tagExpr = ctx.expr(s.Tag)
	}

	// Get default handler (if it exists)
	e = glang.DoExpr{Expr: glang.Tt}
	for _, c := range s.Body.List {
		if c := c.(*ast.CaseClause); c.List == nil {
			e = ctx.stmtList(c.Body, nil)
		}
	}

	for i := len(s.Body.List) - 1; i >= 0; i-- {
		c := s.Body.List[i].(*ast.CaseClause)
		if c.List == nil {
			// default case already handled
			continue
		}

		getCond := func(i int) glang.Expr {
			t := ctx.typeOf(c.List[i])
			eqType := ctx.typeJoin(c.List[i], t, tagType)
			return glang.BinaryExpr{
				X: ctx.handleImplicitConversion(c.List[i], tagType, eqType, glang.IdentExpr("$sw")),
				Op: glang.BinOp{
					OpId: glang.OpEquals,
					Type: ctx.glangType(c.List[i], eqType),
				},
				Y: ctx.handleImplicitConversion(c.List[i], t, eqType, ctx.expr(c.List[i])),
			}
		}

		cond := getCond(0)
		for i := 1; i < len(c.List); i++ {
			cond = glang.BinaryExpr{
				Op: glang.BinOp{
					OpId: glang.OpLOr,
					Type: glang.VerbatimExpr("go.bool"),
				},
				X: getCond(i), Y: cond}
		}

		e = glang.IfExpr{
			Cond: cond,
			Then: ctx.stmtList(c.Body, nil),
			Else: e,
		}
	}

	e = glang.LetExpr{Names: []string{"$sw"}, ValExpr: tagExpr, Cont: e}

	if s.Init != nil {
		e = glang.ParenExpr{Inner: ctx.stmt(s.Init, e)}
	}

	e = glang.SeqExpr{Expr: e, Cont: cont}
	return
}

func (ctx *Ctx) ifStmt(s *ast.IfStmt, cont glang.Expr) glang.Expr {
	var elseExpr glang.Expr = glang.DoExpr{Expr: glang.Tt}
	if s.Else != nil {
		elseExpr = ctx.stmt(s.Else, nil)
	}
	var ife glang.Expr = glang.IfExpr{
		Cond: ctx.handleImplicitConversion(s.Cond, ctx.typeOf(s.Cond), types.Typ[types.Bool], ctx.expr(s.Cond)),
		Then: ctx.blockStmt(s.Body, nil),
		Else: elseExpr,
	}

	if s.Init != nil {
		ife = glang.ParenExpr{Inner: ctx.stmt(s.Init, ife)}
	}
	return glang.SeqExpr{Expr: ife, Cont: cont}
}

func (ctx *Ctx) forStmt(s *ast.ForStmt, cont glang.Expr) glang.Expr {
	var cond glang.Expr = glang.GooseBoolLiteral(true)
	if s.Cond != nil {
		cond = ctx.expr(s.Cond)
	}
	var post glang.Expr = glang.Tt
	if s.Post != nil {
		post = ctx.stmt(s.Post, nil)
	}

	body := ctx.blockStmt(s.Body, nil)
	var e glang.Expr = glang.ForLoopExpr{
		Cond: cond,
		Post: post,
		Body: body,
	}
	if s.Init != nil {
		e = glang.ParenExpr{Inner: ctx.stmt(s.Init, e)}
	}
	return glang.SeqExpr{Expr: e, Cont: cont}
}

func (ctx *Ctx) rangeStmt(s *ast.RangeStmt) glang.Expr {
	var body glang.Expr = ctx.blockStmt(s.Body, nil)
	if s.Key != nil {
		body = ctx.assignFromTo(s.Key, glang.IdentExpr("$key"), body)
	}
	if s.Value != nil {
		body = ctx.assignFromTo(s.Value, glang.IdentExpr("$value"), body)
	}

	var e glang.Expr
	switch t := ctx.typeOf(s.X).Underlying().(type) {
	case *types.Map:
		e = glang.ForRangeMapExpr{
			KeyType:  ctx.glangType(s.X, t.Key()),
			ElemType: ctx.glangType(s.X, t.Elem()),
			Map:      glang.IdentExpr("$range"),
			Body:     body,
		}
	case *types.Slice:
		e = glang.ForRangeSliceExpr{
			Slice: glang.IdentExpr("$range"),
			Ty:    ctx.glangType(s.X, sliceElem(ctx.typeOf(s.X))),
			Body:  body,
		}
	case *types.Chan:
		e = glang.ForRangeChanExpr{
			Chan: glang.IdentExpr("$range"),
			Elem: ctx.glangType(s.X, chanElem(ctx.typeOf(s.X))),
			Body: body,
		}
	default:
		ctx.unsupported(s,
			"range over %v (only maps and slices are supported)",
			ctx.typeOf(s.X).Underlying())
		return nil
	}

	// declare new vars if needed
	if s.Tok == token.DEFINE {
		if s.Key != nil {
			key, ok := s.Key.(*ast.Ident)
			if !ok {
				ctx.nope(s.Key, "expected left side of of `:=` in for range to be an ident")
			}
			if key.Name != "_" {
				t := ctx.glangType(s.Key, ctx.typeOf(s.Key))
				e = glang.LetExpr{
					Names: []string{key.Name},
					ValExpr: glang.NewCallExpr(glang.VerbatimExpr("GoAlloc"), t,
						glang.NewCallExpr(glang.VerbatimExpr("GoZeroVal"), t, glang.Tt)),
					Cont: e,
				}
			}
		}

		if s.Value != nil {
			value, ok := s.Value.(*ast.Ident)
			if !ok {
				ctx.nope(s.Value, "expected left side of of `:=` in for range to be an ident")
			}
			if value.Name != "_" {
				t := ctx.glangType(s.Value, ctx.typeOf(s.Value))
				e = glang.LetExpr{
					Names: []string{value.Name},
					ValExpr: glang.NewCallExpr(glang.VerbatimExpr("GoAlloc"), t,
						glang.NewCallExpr(glang.VerbatimExpr("GoZeroVal"), t, glang.Tt)),
					Cont: e,
				}
			}
		}

		e = glang.ParenExpr{Inner: e}
	}

	switch ctx.typeOf(s.X).Underlying().(type) {
	case *types.Map:
		e = glang.LetExpr{
			Names:   []string{"$range"},
			ValExpr: ctx.expr(s.X),
			Cont:    e,
		}
	case *types.Slice:
		e = glang.LetExpr{
			Names:   []string{"$range"},
			ValExpr: ctx.expr(s.X),
			Cont:    e,
		}
	case *types.Chan:
		e = glang.LetExpr{
			Names:   []string{"$range"},
			ValExpr: ctx.expr(s.X),
			Cont:    e,
		}
	default:
		ctx.unsupported(s,
			"range over %v (only maps and slices are supported)",
			ctx.typeOf(s.X).Underlying())
		return nil
	}

	return e
}

func (ctx *Ctx) defineStmt(s *ast.AssignStmt, cont glang.Expr) glang.Expr {
	e := ctx.assignStmt(s, cont)

	// Before the asignStmt "e", allocate everything that's new in this define stmt.
	for _, lhsExpr := range s.Lhs {
		if ident, ok := lhsExpr.(*ast.Ident); ok {
			if _, ok := ctx.info.Defs[ident]; ok { // if this identifier is defining something
				if ident.Name == "_" {
					continue
				}
				t := ctx.glangType(ident, ctx.info.TypeOf(ident))
				e = glang.LetExpr{
					Names: []string{ident.Name},
					ValExpr: glang.NewCallExpr(glang.VerbatimExpr("GoAlloc"), t,
						glang.NewCallExpr(glang.VerbatimExpr("GoZeroVal"), t, glang.Tt)),
					Cont: e,
				}
			}
		} else {
			ctx.nope(lhsExpr, "defining a non-identifier")
		}
	}

	return e
}

func (ctx *Ctx) varSpec(s *ast.ValueSpec, cont glang.Expr) glang.Expr {
	var lhs []ast.Expr
	for _, l := range s.Names {
		lhs = append(lhs, l)
	}
	return ctx.defineStmt(&ast.AssignStmt{Lhs: lhs, Rhs: s.Values}, cont)
}

// varDeclStmt translates declarations within functions
func (ctx *Ctx) varDeclStmt(s *ast.DeclStmt, cont glang.Expr) glang.Expr {
	decl, ok := s.Decl.(*ast.GenDecl)
	if !ok {
		ctx.noExample(s, "declaration that is not a GenDecl")
	}
	if decl.Tok == token.TYPE {
		// type declarations within a function are obscure but Go does have them
		ctx.unsupported(s, "function type declarations")
	}
	if decl.Tok == token.CONST {
		var expr glang.Expr = cont
		for _, spec := range slices.Backward(decl.Specs) {
			expr = ctx.functionConstSpec(spec.(*ast.ValueSpec), expr)
		}
		return expr
	}
	if decl.Tok == token.VAR {
		var expr glang.Expr = cont
		// TODO: shouldn't this range be reversed?
		for _, spec := range decl.Specs {
			// guaranteed to be a *Ast.ValueSpec due to decl.Tok
			//
			// https://golang.org/pkg/go/ast/#GenDecl
			// TODO: handle TypeSpec
			expr = ctx.varSpec(spec.(*ast.ValueSpec), expr)
		}
		return expr
	}
	ctx.nope(s, "declaration %v within a function (not a type, const, or var)", decl.Tok)
	return nil
}

func (ctx *Ctx) getIndexType(n locatable, t types.Type) types.Type {
	switch t := t.Underlying().(type) {
	case *types.Slice:
		return types.Typ[types.Int]
	case *types.Map:
		return t.Key()
	case *types.Array:
		return types.Typ[types.Int]
	}
	ctx.unsupported(n, "unexpected type for indexing")
	return nil
}

// Returns the address of the given expression.
// Requires that e is actually addressable
func (ctx *Ctx) exprAddr(e ast.Expr) glang.Expr {
	switch e := e.(type) {
	case *ast.ParenExpr:
		return ctx.exprAddr(e.X)
	case *ast.Ident:
		obj := ctx.info.ObjectOf(e)
		if _, ok := obj.(*types.Var); ok {
			if obj.Pkg().Scope() == obj.Parent() {
				return glang.NewCallExpr(glang.VerbatimExpr("GlobalVarAddr"),
					ctx.gallinaIdent(e.Name),
					glang.Tt,
				)
			} else {
				return glang.IdentExpr(e.Name)
			}
		} else {
			ctx.unsupported(e, "exprAddr of ident that is not a var")
		}
	case *ast.IndexExpr:
		targetTy := ctx.typeOf(e.X)
		return glang.NewCallExpr(glang.VerbatimExpr("IndexRef"),
			ctx.glangType(e, targetTy),
			glang.TupleExpr{ctx.expr(e.X),
				ctx.exprIntoType(e.Index, ctx.getIndexType(e.Index, targetTy))})
	case *ast.StarExpr:
		return ctx.expr(e.X)
	case *ast.SelectorExpr:
		return ctx.selectorExprAddr(e)
	default:
		ctx.unsupported(e, "address of unknown expression")
	}
	return nil
}

func (ctx *Ctx) exprIntoType(e ast.Expr, target types.Type) glang.Expr {
	return ctx.handleImplicitConversion(e, ctx.typeOf(e), target, ctx.expr(e))
}

func (ctx *Ctx) assignFromTo(lhs ast.Expr, rhs glang.Expr, cont glang.Expr) glang.Expr {
	// lhs should either be a map index expression, or is addressable
	switch lhs := lhs.(type) {
	case *ast.Ident:
		if lhs.Name == "_" {
			return glang.NewDoSeq(rhs, cont)
		}
	case *ast.IndexExpr:
		targetTy := ctx.typeOf(lhs.X)
		switch t := targetTy.(type) {
		case *types.Map:
			return glang.NewDoSeq(glang.NewCallExpr(glang.VerbatimExpr("map.insert"),
				ctx.glangType(lhs.Index, t.Key()),
				ctx.expr(lhs.X),
				ctx.exprIntoType(lhs.Index, t.Key()),
				rhs), cont)
		}
	}

	return glang.NewDoSeq(glang.StoreStmt{
		Dst: ctx.exprAddr(lhs),
		X:   rhs,
		Ty:  ctx.glangType(lhs, ctx.typeOf(lhs)),
	}, cont)
}

// This handles conversions arising from the notion of "assignability" in the Go spec.
func (ctx *Ctx) handleImplicitConversion(n locatable, from, to types.Type, e glang.Expr) glang.Expr {
	if to == nil {
		// This happens when the LHS is `_`
		return e
	}
	if from == nil {
		ctx.unsupported(n, "implicit conversion: don't know from type")
	}
	if types.Identical(from.Underlying(), to.Underlying()) {
		return e
	} else {
		return glang.NewCallExpr(glang.VerbatimExpr("Convert"),
			ctx.glangType(n, from), ctx.glangType(n, to), e)
	}
}

func (ctx *Ctx) assignStmt(s *ast.AssignStmt, cont glang.Expr) glang.Expr {
	e := cont
	if len(s.Rhs) == 0 {
		return e
	}

	// Execute assignments left-to-right
	for i := len(s.Lhs); i > 0; i-- {
		e = ctx.assignFromTo(s.Lhs[i-1], glang.IdentExpr(fmt.Sprintf("$r%d", i-1)), e)
	}

	// Determine RHS types, specially handling multiple returns from a function call.
	var rhsTypes []types.Type
	for i := 0; i < len(s.Rhs); i++ {
		t := ctx.typeOf(s.Rhs[i])
		if tuple, ok := t.(*types.Tuple); ok {
			for i := range tuple.Len() {
				rhsTypes = append(rhsTypes, tuple.At(i).Type())
			}
		} else {
			rhsTypes = append(rhsTypes, t)
		}
	}

	// collect the RHS expressions
	var rhsExprs []glang.Expr
	if len(s.Rhs) == len(s.Lhs) {
		for _, rhs := range s.Rhs {
			rhsExprs = append(rhsExprs, ctx.expr(rhs))
		}
	} else {
		// RHS is a function call returning multiple things. Will introduce
		// extra let bindings to destructure those multiple returns.
		for i := range s.Lhs {
			rhsExprs = append(rhsExprs, glang.IdentExpr(fmt.Sprintf("$ret%d", i)))
		}
	}

	// Let bindings for RHSs including conversions
	for i := len(s.Lhs); i > 0; i-- {
		e = glang.LetExpr{
			Names: []string{fmt.Sprintf("$r%d", i-1)},
			ValExpr: ctx.handleImplicitConversion(s.Lhs[i-1], rhsTypes[i-1],
				ctx.typeOf(s.Lhs[i-1]), rhsExprs[i-1]),
			Cont: e,
		}
	}

	// Extra let bindings in case RHS is a multiple-returning function
	if len(s.Rhs) != len(s.Lhs) && len(s.Lhs) > 0 {
		var n []string
		for i := range s.Lhs {
			n = append(n, fmt.Sprintf("$ret%d", i))
		}
		e = glang.LetExpr{
			Names:   n,
			ValExpr: ctx.exprSpecial(s.Rhs[0], true),
			Cont:    e,
		}
	}

	return e
}

func (ctx *Ctx) assignOpStmt(s *ast.AssignStmt, cont glang.Expr) glang.Expr {
	// map the assign version to the binary operator
	assignOps := map[token.Token]token.Token{
		token.ADD_ASSIGN: token.ADD,
		token.SUB_ASSIGN: token.SUB,
		token.MUL_ASSIGN: token.MUL,
		token.QUO_ASSIGN: token.QUO,
		token.REM_ASSIGN: token.REM,

		token.AND_ASSIGN:     token.AND,
		token.AND_NOT_ASSIGN: token.AND_NOT,
		token.OR_ASSIGN:      token.OR,
		token.XOR_ASSIGN:     token.XOR,
		token.SHL_ASSIGN:     token.SHL,
		token.SHR_ASSIGN:     token.SHR,
	}
	op, ok := assignOps[s.Tok]
	if !ok {
		ctx.unsupported(s, "unsupported assign+update operation %v", s.Tok)
	}
	// construct s.lhs + s.rhs as a Go AST fragment
	rhs := ctx.binExpr(&ast.BinaryExpr{
		X:  s.Lhs[0],
		Op: op,
		Y:  s.Rhs[0],
	})
	// finish by constructing lhs = rhs
	return ctx.assignFromTo(s.Lhs[0], rhs, cont)
}

func (ctx *Ctx) incDecStmt(stmt *ast.IncDecStmt, cont glang.Expr) glang.Expr {
	opId := glang.OpPlus
	if stmt.Tok == token.DEC {
		opId = glang.OpMinus
	}
	op := glang.BinOp{
		OpId: opId,
		Type: ctx.glangType(stmt.X, ctx.typeOf(stmt.X)),
	}

	one := glang.ZLiteral{Value: big.NewInt(1)}
	var y glang.Expr

	switch t := ctx.typeOf(stmt.X).Underlying().(type) {
	case *types.Basic:
		switch t.Kind() {
		case types.Uint64, types.Int64, types.Int, types.Uint:
			y = glang.Int64Val{Value: one}
		case types.Uint32, types.Int32:
			y = glang.Int32Val{Value: one}
		case types.Uint8, types.Int8:
			y = glang.Int8Val{Value: one}
		}
	default:
		ctx.unsupported(stmt.X, "inc or dec statement with unsupported type %v", ctx.typeOf(stmt.X))
	}
	return ctx.assignFromTo(stmt.X, glang.BinaryExpr{
		X:  ctx.expr(stmt.X),
		Op: op,
		Y:  y,
	}, cont)
}

func (ctx *Ctx) branchStmt(s *ast.BranchStmt, cont glang.Expr) glang.Expr {
	if s.Tok == token.CONTINUE {
		return glang.SeqExpr{Expr: glang.ContinueExpr{}, Cont: cont}
	}
	if s.Tok == token.BREAK {
		return glang.SeqExpr{Expr: glang.BreakExpr{}, Cont: cont}
	}
	ctx.noExample(s, "unexpected control flow %v in loop", s.Tok)
	return nil
}

func (ctx *Ctx) goStmt(e *ast.GoStmt, cont glang.Expr) glang.Expr {
	args := make([]glang.Expr, 0, len(e.Call.Args))
	for i := range len(e.Call.Args) {
		args = append(args, glang.IdentExpr(fmt.Sprintf("$a%d", i)))
	}
	var expr glang.Expr = glang.NewDoSeq(glang.SpawnExpr{Body: glang.NewCallExpr(
		glang.IdentExpr("$go"),
		args...,
	)}, cont)

	expr = glang.LetExpr{
		Names:   []string{"$go"},
		ValExpr: ctx.expr(e.Call.Fun),
		Cont:    expr,
	}

	expr = ctx.callExprPrelude(e.Call, expr)

	return expr
}

func (ctx *Ctx) returnStmt(s *ast.ReturnStmt, cont glang.Expr) glang.Expr {
	if len(s.Results) == 0 {
		return ctx.defaultReturn
	}

	exprs := make([]glang.Expr, 0, len(s.Results))
	var expectedReturnTypes []types.Type
	if ctx.curFuncType.Results() != nil {
		for i := range ctx.curFuncType.Results().Len() {
			expectedReturnTypes = append(expectedReturnTypes, ctx.curFuncType.Results().At(i).Type())
		}
	}

	var retExpr glang.Expr
	func() {
		var unconvertedReturnValues []exprWithInfo
		if len(s.Results) == 1 && len(expectedReturnTypes) > 1 {
			// special case
			tupleType, ok := ctx.typeOf(s.Results[0]).(*types.Tuple)
			if !ok {
				ctx.nope(s.Results[0], "the only way for the number of values in a returnStmt to mismatch "+
					"the function's signature is passing through a multiple-returning function")
			}
			for i := range tupleType.Len() {
				unconvertedReturnValues = append(unconvertedReturnValues, exprWithInfo{
					e: glang.IdentExpr(fmt.Sprintf("$ret%d", i)),
					t: tupleType.At(i).Type(),
					n: s.Results[0],
				})
			}
			defer func() {
				var names []string
				for i := range tupleType.Len() {
					names = append(names, fmt.Sprintf("$ret%d", i))
				}
				retExpr = glang.LetExpr{Names: names,
					ValExpr: glang.ParenExpr{Inner: ctx.expr(s.Results[0])},
					Cont:    retExpr,
				}
			}()
		} else {
			for _, result := range s.Results {
				unconvertedReturnValues = append(unconvertedReturnValues, exprWithInfo{
					e: ctx.expr(result),
					t: ctx.typeOf(result),
					n: result,
				})
			}
		}

		if len(unconvertedReturnValues) != len(expectedReturnTypes) {
			log.Print(len(unconvertedReturnValues), len(expectedReturnTypes))
			log.Print(ctx.curFuncType.Results())
			ctx.nope(s, "bug")
		}

		for i, e := range unconvertedReturnValues {
			exprs = append(exprs, ctx.handleImplicitConversion(e.n, e.t, expectedReturnTypes[i], e.e))
		}
		if len(exprs) == 0 { // return #()
			exprs = []glang.Expr{glang.Tt}
		}
		retExpr = glang.ReturnExpr{Value: glang.TupleExpr(exprs)}
	}()

	return glang.SeqExpr{Expr: retExpr, Cont: cont}
}

func (ctx *Ctx) deferStmt(s *ast.DeferStmt, cont glang.Expr) (expr glang.Expr) {
	ctx.usesDefer = true
	args := make([]glang.Expr, 0, len(s.Call.Args))
	for i := range len(s.Call.Args) {
		args = append(args, glang.IdentExpr(fmt.Sprintf("$a%d", i)))
	}

	expr = glang.LetExpr{
		ValExpr: glang.NewCallExpr(glang.IdentExpr("$f"), args...),
		Cont:    glang.NewCallExpr(glang.IdentExpr("$oldf"), glang.Tt),
	}

	expr = glang.FuncLit{Body: expr}

	expr = glang.LetExpr{
		Names:   []string{"$oldf"},
		ValExpr: glang.DerefExpr{X: glang.IdentExpr("$defer"), Ty: glang.VerbatimExpr("deferType")},
		Cont:    expr,
	}

	expr = glang.StoreStmt{
		Dst: glang.IdentExpr("$defer"),
		Ty:  glang.VerbatimExpr("deferType"),
		X:   expr,
	}

	expr = glang.LetExpr{
		Names:   []string{"$f"},
		ValExpr: ctx.expr(s.Call.Fun),
		Cont:    expr,
	}

	expr = ctx.callExprPrelude(s.Call, expr)
	expr = glang.NewDoSeq(expr, cont)
	return
}

func (ctx *Ctx) selectStmt(s *ast.SelectStmt, cont glang.Expr) (expr glang.Expr) {
	var clauses []glang.CommClause
	var def glang.Expr // nil initially (None)

	var chs []glang.Expr

	// build up select statement itself
	for i, s := range s.Body.List {
		s := s.(*ast.CommClause)
		if s.Comm == nil {
			// a default: case
			def = ctx.stmtList(s.Body, nil)
		} else if c, ok := s.Comm.(*ast.SendStmt); ok {
			chs = append(chs, ctx.expr(c.Chan))

			clauses = append(clauses, glang.CommClause{
				Comm: glang.SendCase{
					ElemType: ctx.glangType(s.Comm, chanElem(ctx.typeOf(c.Chan))),
					Chan:     glang.IdentExpr(fmt.Sprintf("$ch%d", i)),
					Value:    glang.IdentExpr(fmt.Sprintf("$v%d", i)),
				},
				Body: ctx.stmtList(s.Body, nil),
			})
		} else { // must be a receive stmt
			var recvChan glang.Expr
			var chanType types.Type
			body := ctx.stmtList(s.Body, nil)

			// want to figure out the first statment to run in the body
			switch comm := s.Comm.(type) {
			case *ast.ExprStmt:
				recvExpr := comm.X.(*ast.UnaryExpr)
				if recvExpr.Op != token.ARROW {
					ctx.nope(comm.X, "expected recv statement")
				}
				recvChan = ctx.expr(recvExpr.X)
				chanType = ctx.typeOf(recvExpr.X)
				// nothing extra to run in the body
			case *ast.AssignStmt:
				// XXX: replace the RHS in the assignment statement with an
				// ident, so we can put this straight in the the body list
				if len(comm.Rhs) != 1 {
					ctx.nope(comm, "expected a single receive operation on RHS")
				}
				var rhs ast.Expr = comm.Rhs[0]
				for {
					if r, ok := rhs.(*ast.ParenExpr); ok {
						rhs = r.X
					} else {
						break
					}
				}
				recvExpr := rhs.(*ast.UnaryExpr)
				if recvExpr.Op != token.ARROW {
					ctx.nope(comm.Rhs[0], "expected recv statement")
				}
				recvChan = ctx.expr(recvExpr.X)
				chanType = ctx.typeOf(recvExpr.X)

				// XXX: create a new AST node and enough typing information for
				// an assignStmt to translate.
				t := ctx.info.Types[recvExpr]
				comm.Rhs[0] = ast.NewIdent("$recvVal")
				ctx.info.Types[comm.Rhs[0]] = t

				if comm.Tok == token.DEFINE {
					body = ctx.defineStmt(comm, body)
				} else if comm.Tok == token.ASSIGN {
					body = ctx.assignStmt(comm, body)
				}
			default:
				ctx.unsupported(s.Comm, "unexpected statement in select clause")
			}

			chs = append(chs, recvChan)

			clauses = append(clauses, glang.CommClause{
				Comm: glang.RecvCase{
					ElemType: ctx.glangType(s.Comm, chanElem(chanType)),
					Chan:     glang.IdentExpr(fmt.Sprintf("$ch%d", i)),
				},
				Body: glang.FuncLit{
					Args: []glang.Binder{{Name: "$recvVal"}},
					Body: body,
				},
			})
		}
	}

	expr = glang.NewCallExpr(glang.VerbatimExpr("SelectStmt"), glang.SelectStmtClauses{
		Default: def,
		Clauses: clauses,
	})

	for i := len(chs) - 1; i >= 0; i-- {
		expr = glang.LetExpr{
			Names:   []string{fmt.Sprintf("$ch%d", i)},
			ValExpr: chs[i],
			Cont:    expr,
		}

		s := s.Body.List[i].(*ast.CommClause)
		if c, ok := s.Comm.(*ast.SendStmt); ok {
			expr = glang.LetExpr{
				Names:   []string{fmt.Sprintf("$v%d", i)},
				ValExpr: ctx.expr(c.Value),
				Cont:    expr,
			}
		}
	}

	expr = glang.SeqExpr{Expr: expr, Cont: cont}
	return
}

func (ctx *Ctx) sendStmt(s *ast.SendStmt, cont glang.Expr) (expr glang.Expr) {
	elemType := chanElem(ctx.typeOf(s.Chan))
	expr = glang.NewCallExpr(glang.VerbatimExpr("chan.send"),
		ctx.glangType(s, elemType),
		glang.IdentExpr("$chan"),
		glang.IdentExpr("$v"))
	// XXX: left-to-right evaluation, might not match Go
	expr = glang.LetExpr{Names: []string{"$v"},
		ValExpr: ctx.exprIntoType(s.Value, elemType),
		Cont:    expr}
	expr = glang.LetExpr{Names: []string{"$chan"}, ValExpr: ctx.expr(s.Chan), Cont: expr}
	expr = glang.NewDoSeq(expr, cont)
	return
}

func (ctx *Ctx) typeSwitchStmt(s *ast.TypeSwitchStmt, cont glang.Expr) (e glang.Expr) {
	// s.Assign is either y.(type) or x := y.(type); first extract y (an
	// expression) and x (if present)
	var y ast.Expr
	var x *ast.Ident = nil
	switch stmt := s.Assign.(type) {
	case *ast.ExprStmt:
		y = stmt.X.(*ast.TypeAssertExpr).X
	case *ast.AssignStmt:
		if stmt.Tok != token.DEFINE {
			ctx.nope(stmt, "type switch assign not defining a variable")
		}
		y = stmt.Rhs[0].(*ast.TypeAssertExpr).X
		x = stmt.Lhs[0].(*ast.Ident)
	default:
		ctx.nope(stmt, "type switch with unexpected Assign %T", stmt)
	}

	// Get default handler (if it exists)
	e = glang.DoExpr{Expr: glang.Tt}
	for _, c := range s.Body.List {
		if c := c.(*ast.CaseClause); c.List == nil {
			e = ctx.stmtList(c.Body, nil)
			break
		}
	}

	for i := len(s.Body.List) - 1; i >= 0; i-- {
		c := s.Body.List[i].(*ast.CaseClause)
		if c.List == nil {
			// default case already handled
			continue
		}

		body := ctx.stmtList(c.Body, nil)
		if x != nil {
			addAllocation := func(ty glang.Expr) {
				// in switch x := y.(type), we create a mutable variable for x in
				// each case's body, since its value is y coerced to the right type
				// for that case
				body = glang.LetExpr{
					Names: []string{x.Name},
					ValExpr: glang.NewCallExpr(glang.VerbatimExpr("GoAlloc"), ty,
						glang.IdentExpr("$x")),
					Cont: body,
				}
			}
			if len(c.List) > 1 {
				addAllocation(ctx.glangType(y, ctx.typeOf(y)))
			} else {
				// The type of x will depend on the case

				if types.Identical(ctx.typeOf(c.List[0]), types.Typ[types.UntypedNil]) {
					addAllocation(ctx.glangType(y, ctx.typeOf(y)))
				} else {
					addAllocation(ctx.glangType(c.List[0], ctx.typeOf(c.List[0])))
				}
			}
		}

		e = glang.IfExpr{Cond: glang.IdentExpr("$ok"), Then: body, Else: e}

		if len(c.List) > 1 {
			// In this case, the x actually has the same type as y (i.e. x is just y).
			e = glang.LetExpr{Names: []string{"$x"}, ValExpr: glang.IdentExpr("$y"), Cont: e}

			// The case is taken if y can be converted to any of the types
			getCond := func(i int) glang.Expr {
				ty := ctx.typeOf(c.List[i])
				if b, ok := ty.(*types.Basic); ok && b.Kind() == types.UntypedNil {
					return glang.BinaryExpr{
						X: glang.IdentExpr("$y"),
						Op: glang.BinOp{
							OpId: glang.OpEquals,
							Type: ctx.glangType(y, ctx.typeOf(y)),
						},
						Y: glang.VerbatimExpr("#interface.nil"),
					}
				} else {
					return glang.NewCallExpr(glang.VerbatimExpr("Snd"),
						glang.NewCallExpr(glang.VerbatimExpr("TypeAssert2"),
							ctx.glangType(c.List[i], ty),
							glang.IdentExpr("$y"),
						),
					)
				}
			}
			cond := getCond(0)
			for i := range c.List[1:] {
				cond = glang.BinaryExpr{Op: glang.BinOp{
					OpId: glang.OpLOr,
					Type: glang.VerbatimExpr("go.bool"),
				},
					X: getCond(i), Y: cond}
			}
			e = glang.LetExpr{Names: []string{"$ok"}, ValExpr: cond, Cont: e}
		} else {
			// In this case, x should have the type equal to the single type listed in this case.
			ty := ctx.typeOf(c.List[0])
			if b, ok := ty.(*types.Basic); ok && b.Kind() == types.UntypedNil {
				e = glang.LetExpr{Names: []string{"$x"}, ValExpr: glang.IdentExpr("$y"), Cont: e}
				e = glang.LetExpr{
					Names: []string{"$ok"},
					ValExpr: glang.BinaryExpr{
						X: glang.IdentExpr("$y"),
						Op: glang.BinOp{
							OpId: glang.OpEquals,
							Type: ctx.glangType(y, ctx.typeOf(y)),
						},
						Y: glang.VerbatimExpr("#interface.nil"),
					},
					Cont: e,
				}
			} else {
				e = glang.LetExpr{
					Names: []string{"$x", "$ok"},
					ValExpr: glang.NewCallExpr(glang.VerbatimExpr("TypeAssert2"),
						ctx.glangType(c.List[0], ty),
						glang.IdentExpr("$y"),
					),
					Cont: e,
				}
			}
		}
	}
	if s.Init != nil {
		e = glang.ParenExpr{Inner: ctx.stmt(s.Init, e)}
	}
	e = glang.LetExpr{
		Names:   []string{"$y"},
		ValExpr: ctx.expr(y),
		Cont:    e,
	}
	e = glang.SeqExpr{Expr: e, Cont: cont}
	return
}

func (ctx *Ctx) stmt(s ast.Stmt, cont glang.Expr) glang.Expr {
	switch s := s.(type) {
	case *ast.ReturnStmt:
		return ctx.returnStmt(s, cont)
	case *ast.BranchStmt:
		return ctx.branchStmt(s, cont)
	case *ast.IfStmt:
		return ctx.ifStmt(s, cont)
	case *ast.GoStmt:
		return ctx.goStmt(s, cont)
	case *ast.ExprStmt:
		return glang.NewDoSeq(ctx.expr(s.X), cont)
	case *ast.AssignStmt:
		if s.Tok == token.DEFINE {
			return ctx.defineStmt(s, cont)
		} else if s.Tok == token.ASSIGN {
			return ctx.assignStmt(s, cont)
		} else {
			return ctx.assignOpStmt(s, cont)
		}
	case *ast.DeclStmt:
		return ctx.varDeclStmt(s, cont)
	case *ast.IncDecStmt:
		return ctx.incDecStmt(s, cont)
	case *ast.ForStmt:
		// note that this might be a nested loop,
		// in which case the loop var gets replaced by the inner loop.
		return ctx.forStmt(s, cont)
	case *ast.RangeStmt:
		return glang.SeqExpr{Expr: ctx.rangeStmt(s), Cont: cont}
	case *ast.BlockStmt:
		return ctx.blockStmt(s, cont)
	case *ast.SwitchStmt:
		return ctx.switchStmt(s, cont)
	case *ast.TypeSwitchStmt:
		return ctx.typeSwitchStmt(s, cont)
	case *ast.DeferStmt:
		return ctx.deferStmt(s, cont)
	case *ast.SelectStmt:
		return ctx.selectStmt(s, cont)
	case *ast.SendStmt:
		return ctx.sendStmt(s, cont)
	default:
		ctx.unsupported(s, "statement %T", s)
	}
	panic("unreachable")
}

func funcName(f *types.Func) string {
	maybeTypeName := ""
	if recv := f.Type().(*types.Signature).Recv(); recv != nil {
		recvType := recv.Type()
		if ptrType, ok := recvType.(*types.Pointer); ok {
			recvType = ptrType.Elem()
		}
		maybeTypeName = types.TypeString(recvType, func(_ *types.Package) string { return "" }) + "."
	}
	return maybeTypeName + f.Name()
}

// Returns a glang.FuncDecl and maybe also a glang.NameDecl. If the function is an `init` or `_`, this
// returns None.
func (ctx *Ctx) funcDecl(d *ast.FuncDecl) {
	ctx.curFuncType = ctx.typeOf(d.Name).(*types.Signature)
	defer func() {
		ctx.curFuncType = nil
	}()

	funcName := funcName(ctx.info.ObjectOf(d.Name).(*types.Func))
	if funcName == "_" {
		return
	}

	if d.Recv == nil {
		// Always emit func name decl, even if the function is trusted or axiomatized.
		funcId := ctx.info.Defs[d.Name].Pkg().Path() + "." + ctx.info.Defs[d.Name].Name()
		if d.Name.Name != "init" {
			ctx.out.funcDecls = append(ctx.out.funcDecls, glang.ConstDecl{
				Name: d.Name.Name,
				Val:  glang.StringLiteral{Value: funcId},
				Type: glang.VerbatimExpr("go_string"),
			})
			ctx.functions = append(ctx.functions, d)
		}
	}

	if ctx.filter.GetAction(funcName) != declfilter.Translate {
		return
	}

	ctx.usesDefer = false
	var fd glang.FuncDecl
	addSourceDoc(d.Doc, &fd.Comment)
	ctx.addSourceFile(d, &fd.Comment)

	maybeAddReceiver := func() {}
	if d.Recv != nil {
		if len(d.Recv.List) != 1 {
			ctx.nope(d, "function with multiple receivers")
		}
		receiver := d.Recv.List[0]
		recvType := types.Unalias(ctx.typeOf(receiver.Type))
		// recvType must be either a "named" type or a pointer type that points to a named type.
		if baseType, ok := recvType.(*types.Pointer); ok {
			recvType = baseType.Elem()
		}
		namedType, ok := recvType.(*types.Named)
		if !ok {
			ctx.nope(d.Recv, "expected named type as method receiver, got %T", recvType)
		}
		for i := range namedType.TypeArgs().Len() {
			arg := namedType.TypeArgs().At(i)
			if arg, ok := arg.(*types.TypeParam); ok {
				fd.TypeArgs = append(fd.TypeArgs, glang.GallinaIdent(arg.Obj().Name()))
			} else {
				// it doesn't seem possible to have the receiver be a specialized
				// generic type (all args are interpreted as bound parameters)
				ctx.nope(d, "instantiated type argument in function with non-parameter")
			}
		}
		typeName := namedType.Obj().Name()

		fd.Name = glang.TypeMethod(typeName, d.Name.Name)

		name := "_"
		if len(receiver.Names) > 0 {
			name = receiver.Names[0].Name
		}
		fd.RecvArg = &glang.Binder{Name: name}
		if name != "_" && name != "" {
			maybeAddReceiver = func() {
				fd.Body = glang.LetExpr{
					Names: []string{name},
					ValExpr: glang.NewCallExpr(
						glang.VerbatimExpr("GoAlloc"),
						ctx.glangType(receiver, ctx.typeOf(receiver.Type)),
						glang.IdentExpr(name)),
					Cont: fd.Body,
				}
			}
		}
	} else {
		fd.Name = glang.FuncImpl(d.Name.Name)
		switch ctx.filter.GetAction(funcName) {
		case declfilter.Trust:
			return
		case declfilter.Axiomatize:
			return
		}
		if d.Type.TypeParams != nil {
			for _, p := range d.Type.TypeParams.List {
				for _, name := range p.Names {
					fd.TypeArgs = append(fd.TypeArgs, glang.GallinaIdent(name.Name))
				}
			}
		}
	}

	if d.Body == nil {
		ctx.unsupported(d, "external function")
	}

	// Assemble the `defaultReturn` expr so the body's `return` statements can use it.
	var defaultRetExpr glang.TupleExpr
	if d.Type.Results == nil || len(d.Type.Results.List) == 0 {
		defaultRetExpr = append(defaultRetExpr, glang.Tt)
	} else {
		for _, r := range d.Type.Results.List {
			if r.Names == nil {

			} else {
				for _, name := range r.Names {
					defaultRetExpr = append(defaultRetExpr,
						glang.DerefExpr{
							X:  glang.IdentExpr(name.Name),
							Ty: ctx.glangType(r.Type, ctx.typeOf(r.Type)),
						})
				}
			}
		}
	}
	ctx.defaultReturn = glang.ReturnExpr{
		Value: defaultRetExpr,
	}

	var cont glang.Expr = nil
	if d.Type.Results == nil {
		// explicitly return #() at end of void functions
		cont = glang.ReturnExpr{Value: glang.Tt}
	}
	body := ctx.blockStmt(d.Body, cont)

	if d.Name.Name == "init" {
		if ctx.usesDefer {
			body = glang.NewCallExpr(glang.VerbatimExpr("with_defer:"), body)
		} else {
			body = glang.NewCallExpr(glang.VerbatimExpr("exception_do"), body)
		}
		f := glang.FuncLit{Args: nil, Body: body}
		ctx.inits = append(ctx.inits, f)
		return
	}

	fd.Body = body
	var argTypes []glang.Expr
	fd.Args, argTypes = ctx.paramList(d.Type.Params)

	for i, arg := range fd.Args {
		if arg.Name != "_" && arg.Name != "" {
			fd.Body = glang.LetExpr{
				Names: []string{arg.Name},
				ValExpr: glang.NewCallExpr(
					glang.VerbatimExpr("GoAlloc"),
					argTypes[i], glang.IdentExpr(arg.Name)),
				Cont: fd.Body,
			}
		}
	}
	maybeAddReceiver()
	if d.Type.Results != nil {
		for _, r := range d.Type.Results.List {
			t := ctx.glangType(r.Type, ctx.typeOf(r.Type))
			for _, name := range r.Names {
				fd.Body = glang.LetExpr{
					Names: []string{name.Name},
					ValExpr: glang.NewCallExpr(glang.VerbatimExpr("GoAlloc"), t,
						glang.NewCallExpr(glang.VerbatimExpr("GoZeroVal"), t, glang.Tt)),
					Cont: fd.Body,
				}
			}
		}
	}

	if ctx.usesDefer {
		fd.Body = glang.NewCallExpr(glang.VerbatimExpr("with_defer:"), fd.Body)
	} else {
		fd.Body = glang.NewCallExpr(glang.VerbatimExpr("exception_do"), fd.Body)
	}

	ctx.out.funcImplDecls = append(ctx.out.funcImplDecls, fd)
}

// this should only be used for untyped constant literals
func (ctx *Ctx) constantLiteral(e ast.Expr) glang.Expr {
	// FIXME: emit `Convert` rather than doing it all statically here.
	val := ctx.info.Types[e].Value
	if e, ok := e.(*ast.Ident); ok {
		val = ctx.info.ObjectOf(e).(*types.Const).Val()
	}
	v := constant.Val(val)
	t := ctx.typeOf(e)
	constInt := func(cons string) glang.Expr {
		switch v := v.(type) {
		case *big.Int:
			return glang.ToVal{Value: glang.NewCallExpr(glang.VerbatimExpr(cons), glang.ZLiteral{Value: v})}
		case int64:
			return glang.ToVal{Value: glang.NewCallExpr(glang.VerbatimExpr(cons), glang.ZLiteral{Value: big.NewInt(v)})}
		}
		ctx.nope(e, "expected integer constant")
		return nil
	}

	switch t := t.Underlying().(type) {
	case *types.Basic:
		switch t.Kind() {
		case types.Bool, types.UntypedBool:
			return glang.GooseBoolLiteral(v.(bool))
		case types.Uint64, types.Int64, types.Int, types.Uint:
			return constInt("W64")
		case types.Uint32, types.Int32:
			return constInt("W32")
		case types.Uint16, types.Int16:
			return constInt("W16")
		case types.Uint8, types.Int8:
			return constInt("W8")
		case types.String, types.UntypedString:
			return glang.ToVal{Value: glang.StringLiteral{Value: v.(string)}}
		case types.UntypedNil:
			return glang.VerbatimExpr("UntypedNil")
		case types.UntypedInt, types.UntypedRune:
			switch v := v.(type) {
			case *big.Int:
				return glang.ToVal{Value: glang.ZLiteral{Value: v}}
			case int64:
				return glang.ToVal{Value: glang.ZLiteral{Value: big.NewInt(v)}}
			}
		case types.Float64, types.UntypedFloat:
			f, _ := constant.Float64Val(val)
			bits := math.Float64bits(f)
			return glang.Int64Val{Value: glang.ZLiteral{Value: new(big.Int).SetUint64(bits)}}
		case types.Float32:
			f, _ := constant.Float32Val(val)
			bits := math.Float32bits(f)
			return glang.Int32Val{Value: glang.ZLiteral{Value: new(big.Int).SetUint64(uint64(bits))}}
		}
	}
	ctx.unsupported(e, "unsupported constant val")
	return nil
}

// constSpec handles one specification in a const block
func (ctx *Ctx) constSpec(spec *ast.ValueSpec) {
	// Note that a spec is one line, typically something like `C = 1` or maybe just C
	// if using iota, and spec.Names has more than 1 item only for something like
	// `C, D = 2, 3`.
	for i := range spec.Names {
		if spec.Names[i].Name == "_" {
			continue
		}
		switch ctx.filter.GetAction(spec.Names[i].Name) {
		case declfilter.Axiomatize:
			ctx.out.constDecls = append(ctx.out.constDecls, glang.AxiomDecl{DeclName: spec.Names[i].Name,
				Type: glang.VerbatimExpr("val"),
			})
		case declfilter.Translate:
			func() {
				cd := glang.ConstDecl{
					Name: spec.Names[i].Name,
				}
				// copy the line comment only to the first one
				if i == 0 {
					addSourceDoc(spec.Comment, &cd.Comment)
				}
				cd.Val = ctx.constantLiteral(spec.Names[i])
				cd.Type = glang.VerbatimExpr("val")
				ctx.out.constDecls = append(ctx.out.constDecls, cd)
			}()
		}
	}
}

func (ctx *Ctx) constDecl(d *ast.GenDecl) {
	for _, spec := range d.Specs {
		ctx.constSpec(spec.(*ast.ValueSpec))
	}
}

// functionConstSpec translates constant declarations within functions, which
// become GooseLang let bindings (unlike constSpec, which creates Gallina
// definitions); supports untyped ints (unlike varSpec)
func (ctx *Ctx) functionConstSpec(spec *ast.ValueSpec, cont glang.Expr) glang.Expr {
	var e glang.Expr = cont
	// Note that a spec is one line, typically something like `C = 1` or maybe just C
	// if using iota, and spec.Names has more than 1 item only for something like
	// `C, D = 2, 3`.

	// reverse iteration order because each expression uses the previous as a
	// continuation
	for i := len(spec.Names) - 1; i >= 0; i-- {
		if spec.Names[i].Name == "_" {
			continue
		}
		constVal := ctx.constantLiteral(spec.Names[i])
		e = glang.GallinaLetExpr{
			Name:    spec.Names[i].Name,
			ValExpr: constVal,
			Cont:    e,
		}
	}
	return e
}

func (ctx *Ctx) globalVarDecl(d *ast.GenDecl) {
	for _, spec := range d.Specs {
		s := spec.(*ast.ValueSpec)
		for _, name := range s.Names {
			if name.Name == "_" {
				continue
			}
			ctx.out.varDecls = append(ctx.out.varDecls, glang.ConstDecl{
				Name: name.Name,
				Val: glang.StringLiteral{
					Value: ctx.info.Defs[name].Pkg().Path() + "." + ctx.info.Defs[name].Name(),
				},
				Type: glang.VerbatimExpr("go_string"),
			})
			switch ctx.filter.GetAction(name.Name) {
			case declfilter.Translate:
				ctx.globalVars = append(ctx.globalVars, name)
			default:
				if s.Values != nil {
					ctx.out.varDecls = append(ctx.out.varDecls, glang.AxiomDecl{
						DeclName: name.Name + "'init",
						Type:     glang.VerbatimExpr("val"),
					})
				}
			}
		}
	}
}

func stringLitValue(lit *ast.BasicLit) string {
	if lit.Kind != token.STRING {
		panic("unexpected non-string literal")
	}
	s, err := strconv.Unquote(lit.Value)
	if err != nil {
		panic("unexpected string literal value: " + err.Error())
	}
	return s
}

var ffiMapping = map[string]string{
	"github.com/mit-pdos/gokv/grove_ffi":         "grove",
	"github.com/goose-lang/primitive/disk":       "disk",
	"github.com/goose-lang/primitive/async_disk": "async_disk",
}

func (ctx *Ctx) imports(d []ast.Spec) {
	for _, s := range d {
		s := s.(*ast.ImportSpec)
		importPath := stringLitValue(s.Path)
		if !ctx.filter.ShouldImport(importPath) {
			continue
		}

		n := ctx.info.PkgNameOf(s)
		if _, ok := ctx.importNames[n.Imported().Path()]; !ok {
			ctx.importNames[n.Imported().Path()] = n
			ctx.importNamesOrdered = append(ctx.importNamesOrdered, n)
			ctx.out.importDecls = append(ctx.out.importDecls, glang.ImportDecl{Path: importPath})
		}
	}
}

func (ctx *Ctx) decl(d ast.Decl) {
	switch d := d.(type) {
	case *ast.FuncDecl:
		ctx.funcDecl(d)
	case *ast.GenDecl:
		switch d.Tok {
		case token.IMPORT:
			ctx.imports(d.Specs)
		case token.CONST:
			ctx.constDecl(d)
		case token.VAR:
			ctx.globalVarDecl(d)
		case token.TYPE:
			for _, spec := range d.Specs {
				ctx.typeDecl(spec.(*ast.TypeSpec))
			}
		default:
			ctx.nope(d, "unknown token type in decl")
		}
	case *ast.BadDecl:
		ctx.nope(d, "bad declaration in type-checked code")
	default:
		ctx.nope(d, "top-level decl")
	}
}

func (ctx *Ctx) packagePropClass() []glang.Decl {
	var decls = []glang.Decl{}

	// top-level decl
	w := new(strings.Builder)
	fmt.Fprintf(w, "Class Assumptions%s `{!GoGlobalContext} `{!GoLocalContext} `{!GoSemanticsFunctions} : Prop :=\n",
		ctx.declImplicitParams,
	)
	fmt.Fprintln(w, "{")

	// toposort named types specs
	nameToTypeSpecMap := make(map[string]*ast.TypeSpec)
	for _, t := range ctx.namedTypeSpecs {
		nameToTypeSpecMap[t.Name.Name] = t
		fmt.Fprintln(w, "  #[global] "+t.Name.Name+"_instance :: "+t.Name.Name+"_Assumptions;")
	}
	for t := range toposort.ToposortSeq(slices.Values(ctx.namedTypeSpecs),
		func(s *ast.TypeSpec) iter.Seq[*ast.TypeSpec] {
			return func(yield func(s *ast.TypeSpec) bool) {
				if ctx.filter.GetAction(s.Name.Name) == declfilter.Axiomatize {
					return
				}
				for n := range util.TypeGetDependencies(ctx.pkgPath, ctx.typeOf(s.Type)) {
					if t, ok := nameToTypeSpecMap[n]; ok {
						if !yield(t) {
							return
						}
					}
				}
			}
		},
		func(cycle []*ast.TypeSpec) {
			s := "cycle: "
			sep := ""
			for _, t := range cycle {
				s += sep + t.Name.Name
				sep = "-> "
			}
			ctx.unsupported(cycle[0], "%s", s)
		}) {
		decls = append(decls, ctx.namedTypeSemanticsDecl(t)...)
	}

	for _, f := range ctx.functions {
		if ctx.filter.GetAction(f.Name.Name) == declfilter.Axiomatize {
			continue
		}

		typeParams := ""
		typeArgList, sep := "[", ""
		if f.Type.TypeParams != nil {
			for _, p := range f.Type.TypeParams.List {
				for _, name := range p.Names {
					typeParams += (" " + name.Name)
					typeArgList += sep + name.Name
					sep = "; "
				}
			}
		}
		typeArgList += "]"

		impl := glang.FuncImpl(f.Name.Name)
		fmt.Fprintf(w, "  #[global] %s_unfold%s :: FuncUnfold %s %s (%s%s);\n",
			f.Name.Name, typeParams, f.Name.Name, typeArgList, impl, typeParams)
	}

	for _, impName := range ctx.importNamesOrdered {
		fmt.Fprintf(w, "  #[global] import_%[1]s_Assumption :: %[1]s.Assumptions;\n", impName.Imported().Name())
	}

	fmt.Fprint(w, "}.")

	topDecl := glang.VerbatimDecl{
		Content: w.String(),
	}
	decls = append(decls, topDecl)

	return decls
}

// After using Ctx to translate every decl, this will return the extra decls
// that should be added to the accumulated set of glang.Decls.
func (ctx *Ctx) finalExtraDecls() {
	var decls = []glang.Decl{}

	infoContents := fmt.Sprintf("#[global] Instance info' : PkgInfo %s :=\n", ctx.pkgIdent) +
		"{|\n  pkg_imported_pkgs := ["
	sep := ""
	for _, impName := range ctx.importNamesOrdered {
		pkg := impName.Imported()
		infoContents += sep + fmt.Sprintf("code.%s.pkg_id.%s", strings.ReplaceAll(glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkg.Path()), "/", "."), pkg.Name())
		sep = "; "
	}
	infoContents += "]\n|}."
	infoInstanceDecl := glang.VerbatimDecl{
		Content: infoContents,
	}
	decls = append(decls, infoInstanceDecl)

	initFunc := glang.FuncDecl{Name: "initialize'"}

	var e glang.Expr

	// add all init() function bodies
	for i := range ctx.inits {
		init := ctx.inits[len(ctx.inits)-i-1]
		e = glang.NewDoSeq(glang.NewCallExpr(init, glang.Tt), e)
	}

	if ctx.filter.GetAction("_") != declfilter.Translate {
		decls = append(decls, glang.AxiomDecl{
			DeclName: "_'init",
			Type:     glang.VerbatimExpr("val"),
		})
	}

	// initialize all global vars
InitLoop:
	for i := range ctx.info.InitOrder {
		init := ctx.info.InitOrder[len(ctx.info.InitOrder)-i-1]

		// Check if any of the LHS variables should be treated as axiomatized
		for i := 0; i < len(init.Lhs); i++ {
			varName := init.Lhs[i].Name()
			if ctx.filter.GetAction(varName) != declfilter.Translate {
				e = glang.NewDoSeq(
					glang.NewCallExpr(ctx.gallinaIdent(varName+"'init"), glang.Tt),
					e)
				continue InitLoop
			}
		}

		// Execute assignments left-to-right
		for i := len(init.Lhs); i > 0; i-- {
			if init.Lhs[i-1].Name() != "_" {
				e = glang.NewDoSeq(
					glang.StoreStmt{
						Dst: glang.NewCallExpr(glang.VerbatimExpr("GlobalVarAddr"),
							ctx.gallinaIdent(init.Lhs[i-1].Name()), glang.Tt,
						),
						X:  glang.IdentExpr(fmt.Sprintf("$r%d", i-1)),
						Ty: ctx.glangType(init.Lhs[i-1], init.Lhs[i-1].Type()),
					}, e)
			}
		}
		if e == nil {
			e = glang.DoExpr{Expr: glang.Tt}
		}

		// Determine RHS types, specially handling multiple returns from a function call.
		var rhsTypes []types.Type
		t := ctx.typeOf(init.Rhs)
		if tuple, ok := t.(*types.Tuple); ok {
			for i := range tuple.Len() {
				rhsTypes = append(rhsTypes, tuple.At(i).Type())
			}
		} else {
			rhsTypes = append(rhsTypes, t)
		}

		// collect the RHS expressions
		var rhsExprs []glang.Expr
		if 1 == len(init.Lhs) {
			rhsExprs = append(rhsExprs, ctx.expr(init.Rhs))
		} else {
			// RHS is a function call returning multiple things. Will introduce
			// extra let bindings to destructure those multiple returns.
			for i := range init.Lhs {
				rhsExprs = append(rhsExprs, glang.IdentExpr(fmt.Sprintf("$ret%d", i)))
			}
		}

		// Let bindings for RHSs including conversions
		for i := len(init.Lhs); i > 0; i-- {
			e = glang.LetExpr{
				Names: []string{fmt.Sprintf("$r%d", i-1)},
				ValExpr: ctx.handleImplicitConversion(init.Lhs[i-1], rhsTypes[i-1],
					init.Lhs[i-1].Type(), rhsExprs[i-1]),
				Cont: e,
			}
		}

		// Extra let bindings in case RHS is a multiple-returning function
		if 1 != len(init.Lhs) {
			var n []string
			for i := range init.Lhs {
				n = append(n, fmt.Sprintf("$ret%d", i))
			}
			e = glang.LetExpr{
				Names:   n,
				ValExpr: ctx.exprSpecial(init.Rhs, true),
				Cont:    e,
			}
		}
	}

	for _, importName := range ctx.importNamesOrdered {
		e = glang.NewDoSeq(
			glang.NewCallExpr(
				ctx.gallinaIdent(importName.Imported().Name()+"."+"initialize'"),
				glang.Tt),
			e)
	}

	if e == nil {
		e = glang.DoExpr{Expr: glang.Tt}
	}

	for _, varIdent := range ctx.globalVars {
		e = glang.NewDoSeq(
			glang.NewCallExpr(
				glang.VerbatimExpr("go.GlobalAlloc"),
				glang.GallinaIdent(varIdent.Name),
				ctx.glangType(varIdent, ctx.typeOf(varIdent)),
				glang.Tt,
			),
			e)
	}

	e = glang.NewCallExpr(glang.VerbatimExpr("exception_do"), e)
	e = glang.NewCallExpr(glang.VerbatimExpr("package.init"),
		ctx.gallinaIdent(ctx.pkgIdent),
		glang.FuncLit{Args: nil, Body: e},
	)

	initFunc.Body = e
	decls = append(decls, initFunc)

	decls = append(decls, ctx.packagePropClass()...)
	ctx.out.finalDecls = decls
}
