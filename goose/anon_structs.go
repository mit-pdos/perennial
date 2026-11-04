package goose

import (
	"fmt"
	"go/types"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/mit-pdos/perennial/goose/util"
	"golang.org/x/tools/go/packages"
)

// An unnamed struct type with fields is modeled like a defined struct type: a
// structure models its values (named util.AnonStructName), its field list is
// X.fields and its go.GoType X.underlying (a struct type, with no go.Named
// around it), and its TypeAssumptions class has its type representation and
// field steps. The package declares these for every unnamed struct type its
// translation mentions; two packages mentioning the same type each have their
// own structure, for the same go.GoType.
type anonStruct struct {
	name   string
	key    string
	t      *types.Struct
	params []string // the type parameters it mentions (util.AnonStructParams)
	fields glang.StructType
	// its structure and TypeAssumptions class are emitted
	emitted bool
}

// anonStructOf registers the unnamed struct type t (with fields), after the
// ones its fields mention.
func (ctx *Ctx) anonStructOf(n locatable, t *types.Struct) *anonStruct {
	name := util.AnonStructName(t)
	key := types.TypeString(t, func(p *types.Package) string { return p.Path() })
	if a, ok := ctx.anonStructs[name]; ok {
		if a.key != key {
			ctx.nope(n, "unnamed struct types %s and %s have the same name %s", a.key, key, name)
		}
		return a
	}
	for i := range t.NumFields() {
		if t.Tag(i) != "" {
			ctx.unsupported(n, "struct tag on a struct type that is not a defined type")
		}
	}
	// the package's aliases are declared after the unnamed struct types (an
	// alias may denote one), so the field types spell them out
	saved := ctx.inAnonStructFields
	ctx.inAnonStructFields = true
	fields := ctx.structType(t)
	ctx.inAnonStructFields = saved
	var params []string
	for _, p := range util.AnonStructParams(t) {
		params = append(params, p.Obj().Name())
	}
	a := &anonStruct{name: name, key: key, t: t, params: params, fields: fields}
	ctx.anonStructs[name] = a
	ctx.anonStructOrder = append(ctx.anonStructOrder, a)
	return a
}

// anonStructTypeDecls are the field list and go.GoType of a.
func (ctx *Ctx) anonStructTypeDecls(a *anonStruct) []glang.Decl {
	var fdsArg glang.Expr = glang.TermIdent(a.name + "'fds")
	if len(a.params) > 0 {
		var args []glang.Expr
		for _, p := range a.params {
			args = append(args, glang.TermIdent(p))
		}
		fdsArg = glang.CallExpr{MethodName: fdsArg, Args: args}
	}
	return []glang.Decl{
		glang.VerbatimDecl{Content: ctx.leanFdsDecl(a.name, a.params, a.fields)},
		glang.TypeDecl{
			Name:       glang.TypeImpl(a.name),
			Body:       glang.CallExpr{MethodName: glang.VerbatimExpr("go.StructType"), Args: []glang.Expr{fdsArg}},
			TypeParams: a.params,
		},
	}
}

// anonStructDecls emits the structure and TypeAssumptions class of a, after
// those of the unnamed struct types that are part of its values.
func (ctx *Ctx) anonStructDecls(a *anonStruct) []glang.Decl {
	if a.emitted {
		return nil
	}
	a.emitted = true
	var decls []glang.Decl
	for i := range a.t.NumFields() {
		decls = append(decls, ctx.anonStructsByValueDecls(a.t.Field(i).Type())...)
	}
	n := ctx.anonStructPos(a)
	ns := glang.LeanIdent(a.name)
	decls = append(decls, glang.VerbatimDecl{Content: ctx.leanStructureDecl(n, ns, a.params, a.t)})

	goBinders := leanTypeParamBinders(a.params, "go.GoType")
	valBinders := leanTypeParamBinders(primed(a.params), "Type")
	implTy := leanApplied(glang.LeanIdent(glang.TypeImpl(a.name)), a.params)
	valTy := leanApplied(ns, primed(a.params))
	var fields []leanClassField
	add := func(name, ty string) {
		fields = append(fields, leanClassField{name: name, ty: ty})
	}
	binders := ""
	if len(a.params) > 0 {
		binders = goBinders + " " + valBinders
		for _, p := range a.params {
			pi, pi_ := glang.LeanIdent(p), glang.LeanIdent(p+"'")
			binders += fmt.Sprintf(" [ZeroVal %s] [TypeRepr %s %s]", pi_, pi, pi_)
		}
	}
	add("type_repr", leanForall(binders, fmt.Sprintf("go.TypeReprUnderlying %s %s", implTy, valTy)))
	ctx.structFieldAssumptions(n, a.t, valTy, implTy, goBinders, valBinders, add)
	decls = append(decls, typeAssumptionsDecl{
		VerbatimDecl: glang.VerbatimDecl{Content: leanClass(glang.LeanEncodedName(a.name+"_Assumptions"),
			" [GooseExts] "+leanClassParams, fields)},
		fields: len(fields),
	})
	return decls
}

// anonStructsByValueDecls emits the unnamed struct types that are part of
// the values of t (util.AnonStructsByValue).
func (ctx *Ctx) anonStructsByValueDecls(t types.Type) []glang.Decl {
	var decls []glang.Decl
	for _, s := range util.AnonStructsByValue(t) {
		if a, ok := ctx.anonStructs[util.AnonStructName(s)]; ok {
			decls = append(decls, ctx.anonStructDecls(a)...)
		}
	}
	return decls
}

// anonStructPos is a position to report an error about a at: its first field.
func (ctx *Ctx) anonStructPos(a *anonStruct) locatable {
	return a.t.Field(0)
}

// AnonStruct is an unnamed struct type of a package's translation, as proofgen
// needs it.
type AnonStruct struct {
	Name       string
	Struct     *types.Struct
	TypeParams []string
}

// AnonStructs are the unnamed struct types (with fields) the translation of
// pkg (with the declaration filter filter) mentions, each after the ones its
// fields mention: those whose structures the translation declares.
func AnonStructs(pkg *packages.Package, filter declfilter.DeclFilter) []AnonStruct {
	ctx := NewPkgCtx(pkg, filter)
	ctx.files(pkg.Syntax)
	var out []AnonStruct
	for _, a := range ctx.anonStructOrder {
		out = append(out, AnonStruct{Name: a.name, Struct: a.t, TypeParams: a.params})
	}
	return out
}
