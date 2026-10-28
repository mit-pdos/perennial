package goose

// The declarations that are emitted as verbatim Lean text (see types.go and
// goose.go).

import (
	"fmt"
	"go/ast"
	"go/types"
	"strings"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/glang"
)

const leanClassParams = "[GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]"

// leanClassField is a field of an Assumptions class; all fields are declared
// instances.
type leanClassField struct {
	name string
	ty   string
}

func leanClass(name string, params string, fields []leanClassField) string {
	w := new(strings.Builder)
	fmt.Fprintf(w, "class %s%s : Prop", name, params)
	if len(fields) == 0 {
		return w.String()
	}
	fmt.Fprint(w, " where")
	var names []string
	for _, f := range fields {
		fname := glang.LeanQuoteComponent(f.name)
		fmt.Fprintf(w, "\n  %s : %s", fname, f.ty)
		names = append(names, name+"."+fname)
	}
	fmt.Fprintf(w, "\n\nattribute [instance] %s", strings.Join(names, "\n  "))
	return w.String()
}

func leanTypeParamBinders(params []string, ty string) string {
	if len(params) == 0 {
		return ""
	}
	var ps []string
	for _, p := range params {
		ps = append(ps, glang.LeanIdent(p))
	}
	return "(" + strings.Join(ps, " ") + " : " + ty + ")"
}

func leanForall(binders string, body string) string {
	if binders == "" {
		return body
	}
	return "∀ " + binders + ", " + body
}

func (ctx *Ctx) namedTypeParams(spec *ast.TypeSpec) []string {
	namedType := ctx.typeOf(spec.Name).(*types.Named)
	var params []string
	if tps := namedType.TypeParams(); tps != nil {
		for i := range tps.Len() {
			params = append(params, tps.At(i).Obj().Name())
		}
	}
	return params
}

// leanApplied renders `f a1 ... an` (with f and ai identifiers)
func leanApplied(f string, args []string) string {
	if len(args) == 0 {
		return f
	}
	var as []string
	for _, a := range args {
		as = append(as, glang.LeanIdent(a))
	}
	return "(" + f + " " + strings.Join(as, " ") + ")"
}

func primed(xs []string) []string {
	var ys []string
	for _, x := range xs {
		ys = append(ys, x+"'")
	}
	return ys
}

// namedLeanTypeDecl is the Lean type modeling values of the Go named type, in a
// namespace named after the type.
func (ctx *Ctx) namedLeanTypeDecl(spec *ast.TypeSpec) string {
	w := new(strings.Builder)
	ns := glang.LeanIdent(spec.Name.Name)
	params := ctx.namedTypeParams(spec)
	typeBinders := leanTypeParamBinders(params, "Type")
	tApplied := leanApplied(ns, params)

	switch ctx.filter.GetAction(spec.Name.Name) {
	case declfilter.Axiomatize:
		fmt.Fprintf(w, "axiom %s : %s\n", ns, leanForall(typeBinders, "Type"))
		zvBinders := ""
		if len(params) > 0 {
			zvBinders = "{" + strings.TrimSuffix(strings.TrimPrefix(typeBinders, "("), ")") + "}"
			for _, p := range params {
				zvBinders += " [ZeroVal " + glang.LeanIdent(p) + "]"
			}
		}
		fmt.Fprintf(w, "axiom %s.zero_val : %s\n", ns, leanForall(zvBinders, "ZeroVal "+tApplied))
		fmt.Fprintf(w, "attribute [instance] %s.zero_val", ns)
	case declfilter.Translate:
		switch t := ctx.typeOf(spec.Type).(type) {
		case *types.Struct:
			sep := ""
			if typeBinders != "" {
				sep = " "
			}
			fmt.Fprintf(w, "structure %s [GooseExts]%s%s where\n  mk ::\n", ns, sep, typeBinders)
			for i := range t.NumFields() {
				f := t.Field(i)
				ft := ctx.toLeanType(spec, f.Type())
				fmt.Fprintf(w, "  %s : %s\n", glang.LeanQuoteComponent(recordProjection(i, f.Name())), ft)
			}
			zvBinders := ""
			if len(params) > 0 {
				zvBinders = " {" + strings.TrimSuffix(strings.TrimPrefix(typeBinders, "("), ")") + "}"
				for _, p := range params {
					zvBinders += " [ZeroVal " + glang.LeanIdent(p) + "]"
				}
			}
			fmt.Fprintf(w, "\nnoncomputable instance %s.zero_val [GooseExts]%s : ZeroVal %s :=\n  ⟨%s.mk", ns, zvBinders, tApplied, ns)
			for range t.NumFields() {
				fmt.Fprint(w, " zeroValDef")
			}
			fmt.Fprint(w, "⟩")
		default:
			sep := ""
			if typeBinders != "" {
				sep = " "
			}
			fmt.Fprintf(w, "abbrev %s [GooseExts]%s%s : Type := %s", ns, sep, typeBinders, ctx.toLeanType(spec, t))
		}
	}
	return w.String()
}

// leanFdsDecl declares the field list of a struct type: X.fieldsUnsealed, and
// X.fields, an irreducible copy.
func (ctx *Ctx) leanFdsDecl(spec *ast.TypeSpec, ty glang.StructType) string {
	name := spec.Name.Name
	params := ctx.typeParamList(spec.TypeParams)
	binders := ""
	if len(params) > 0 {
		binders = " " + leanTypeParamBinders(params, "go.GoType")
	}
	fds := glang.LeanEncodedName(name + "'fds")
	fdsU := glang.LeanEncodedName(name + "'fds_unsealed")
	w := new(strings.Builder)
	fmt.Fprintf(w, "@[reducible] noncomputable def %s [GooseExts] [GoGlobalContext]%s : List go.field_decl :=\n  %s\n", fdsU, binders,
		ty.LeanFields())
	fmt.Fprintf(w, "\n@[irreducible] noncomputable def %s [GooseExts] [GoGlobalContext]%s : List go.field_decl :=\n  %s\n",
		fds, binders, leanApplied(fdsU, params))
	fmt.Fprintf(w, "\nnoncomputable instance %s [GooseExts] [GoGlobalContext]%s :\n    EqualsUnfold %s %s :=\n  ⟨by unfold %s; rfl⟩",
		glang.LeanQuoteComponent("equals_unfold_"+name), binders, leanApplied(fds, params),
		leanApplied(fdsU, params), fds)
	return w.String()
}

func (ctx *Ctx) leanStructImplBody(spec *ast.TypeSpec) glang.Expr {
	var fdsArg glang.Expr = glang.TermIdent(spec.Name.Name + "'fds")
	params := ctx.typeParamList(spec.TypeParams)
	if len(params) > 0 {
		var args []glang.Expr
		for _, p := range params {
			args = append(args, glang.TermIdent(p))
		}
		fdsArg = glang.CallExpr{MethodName: fdsArg, Args: args}
	}
	return glang.CallExpr{MethodName: glang.VerbatimExpr("go.StructType"), Args: []glang.Expr{fdsArg}}
}

// typeAssumptionsDecl is the class of assumptions about a named type. Only the
// package's Assumptions class refers to it, so a large package's classes go in
// modules of their own (see leanChunks).
type typeAssumptionsDecl struct {
	glang.VerbatimDecl
	fields int
}

// packageAssumptionsDecl is the package-level Assumptions class.
type packageAssumptionsDecl struct {
	glang.VerbatimDecl
}

// namedTypeLeanPropClassDecl is the class of assumptions about a named type
// (X.TypeAssumptions): its type representation, its underlying type, the struct
// field accessors and its method set.
func (ctx *Ctx) namedTypeLeanPropClassDecl(spec *ast.TypeSpec) typeAssumptionsDecl {
	typeName := spec.Name.Name
	descName := glang.LeanTypeDesc(typeName)
	implName := glang.LeanIdent(glang.TypeImpl(glang.ToIdent(typeName)))

	t := ctx.typeOf(spec.Name).(*types.Named)
	tunder := ctx.typeOf(spec.Type)

	// t applied to its own type parameters: its methods' signatures are in
	// those parameters, not in the names each receiver gives them
	var params []string
	if t.TypeParams() != nil {
		var targs []types.Type
		for i := range t.TypeParams().Len() {
			params = append(params, t.TypeParams().At(i).Obj().Name())
			targs = append(targs, t.TypeParams().At(i))
		}
		inst, _ := types.Instantiate(nil, t, targs, false)
		t = inst.(*types.Named)
	}
	goBinders := leanTypeParamBinders(params, "go.GoType")
	valBinders := leanTypeParamBinders(primed(params), "Type")

	var fields []leanClassField
	add := func(name, ty string) {
		fields = append(fields, leanClassField{name: name, ty: ty})
	}

	implTy := leanApplied(implName, params)
	ty := leanApplied(descName, params)
	valTy := leanApplied(glang.LeanIdent(typeName), primed(params))

	// type repr instance
	if _, ok := ctx.typeOf(spec.Type).(*types.Struct); ok ||
		ctx.filter.GetAction(typeName) == declfilter.Axiomatize {
		binders := ""
		if len(params) > 0 {
			binders = goBinders + " " + valBinders
			for _, p := range params {
				pi, pi_ := glang.LeanIdent(p), glang.LeanIdent(p+"'")
				binders += fmt.Sprintf(" [ZeroVal %s] [TypeRepr %s %s]", pi_, pi, pi_)
			}
		}
		add("type_repr", leanForall(binders, fmt.Sprintf("go.TypeReprUnderlying %s %s", implTy, valTy)))
	}

	// underlying instance
	add("underlying", leanForall(goBinders, fmt.Sprintf("go.UnderlyingDirectedEq %s %s", ty, implTy)))
	if ctx.filter.GetAction(typeName) == declfilter.Axiomatize {
		add("isUnderlying",
			leanForall(goBinders, fmt.Sprintf("go.IsUnderlying %s %s", implTy, implTy)))
	}

	// maybe emit StructFieldSet and StructFieldGet instances
	if ctx.filter.GetAction(t.Obj().Name()) == declfilter.Translate {
		if st, ok := tunder.(*types.Struct); ok {
			for i := range st.NumFields() {
				fieldName := fieldName(i, st.Field(i).Name())
				projName := glang.LeanQuoteComponent(recordProjection(i, st.Field(i).Name()))
				fieldTy := ctx.toLeanTypeP(spec, st.Field(i).Type(), true)
				xBinder := goBinders
				if valBinders != "" {
					xBinder += " " + valBinders
				}
				if xBinder != "" {
					xBinder += " "
				}
				add("get_"+fieldName, fmt.Sprintf(
					"∀ %s(x : %s), go.IsGoStepPureDetTagged under (StructFieldGet %s %s) #x (Val #(x.%s))",
					xBinder, valTy, implTy, glang.LeanStringLit(fieldName), projName))
				add("set_"+fieldName, fmt.Sprintf(
					"∀ %s(x : %s) (y : %s), go.IsGoStepPureDetTagged under (StructFieldSet %s %s) (PairV #x #y) (Val #(({ x with %s := y } : %s)))",
					xBinder, valTy, fieldTy, implTy, glang.LeanStringLit(fieldName), projName, valTy))
			}
		}
	}

	ptrTy := "(go.GoType.PointerType " + ty + ")"

	// the method sets of `t` and `*t`, as go/types computes them (the methods
	// declared with either receiver, and those promoted through embedded fields)
	goMset := types.NewMethodSet(t)
	goPtrMset := types.NewMethodSet(types.NewPointer(t))
	add("method_set", leanForall(goBinders, fmt.Sprintf("go.MethodSetIs %s %s",
		ty, ctx.leanMethodSet(t.Obj(), goMset))))
	add("ptr_method_set", leanForall(goBinders, fmt.Sprintf("go.MethodSetIs %s %s",
		ptrTy, ctx.leanMethodSet(t.Obj(), goPtrMset))))

	if !types.IsInterface(t) {
		// for every method in `t`
		for i := range goMset.Len() {
			selection := goMset.At(i)
			methodName, index := selection.Obj().Name(), selection.Index()
			if ctx.filter.GetAction(typeName+"."+methodName) == declfilter.Axiomatize {
				continue
			}
			var impl string
			if len(index) == 0 {
				ctx.nope(t.Obj(), "expected non-empty index in methodSet translation")
			} else if len(index) == 1 {
				impl = leanApplied(glang.LeanIdent(glang.TypeMethod(typeName, methodName)), params)
			} else {
				structType, ok := t.Underlying().(*types.Struct)
				if !ok {
					ctx.nope(t.Obj(), "type with embedded method should be a struct")
				}
				field := structType.Field(index[0])
				impl = glang.FuncLit{
					Args: []glang.Binder{{Name: "$r"}},
					Body: glang.NewCallExpr(glang.VerbatimExpr("MethodResolve"),
						ctx.glangType(field, field.Type()),
						glang.StringLiteral{Value: methodName},
						glang.NewCallExpr(glang.VerbatimExpr("StructFieldGet"),
							glang.VerbatimExpr(ty), glang.StringLiteral{Value: field.Name()},
							glang.IdentExpr("$r"))),
				}.LeanVal()
			}
			add(methodName+"_unfold",
				leanForall(goBinders, fmt.Sprintf("MethodUnfold %s %s %s", ty, glang.LeanStringLit(methodName), lparenS(impl))))
		}

		// for every method in `*t`
		for i := range goPtrMset.Len() {
			selection := goPtrMset.At(i)
			methodName, index := selection.Obj().Name(), selection.Index()
			if ctx.filter.GetAction(typeName+"."+methodName) == declfilter.Axiomatize {
				continue
			}
			var impl string
			if len(index) == 0 {
				ctx.nope(t.Obj(), "expected non-empty index in methodSet translation")
			} else if len(index) == 1 {
				recvType := t.Method(index[0]).Signature().Recv().Type()
				if _, recvIsPointer := recvType.(*types.Pointer); recvIsPointer {
					impl = leanApplied(glang.LeanIdent(glang.TypeMethod(typeName, methodName)), params)
				} else {
					impl = glang.FuncLit{
						Args: []glang.Binder{{Name: "$r"}},
						Body: glang.NewCallExpr(glang.VerbatimExpr("MethodResolve"),
							glang.VerbatimExpr(ty), glang.StringLiteral{Value: methodName},
							glang.DerefExpr{X: glang.IdentExpr("$r"), Ty: glang.VerbatimExpr(ty)}),
					}.LeanVal()
				}
			} else {
				structType, ok := t.Underlying().(*types.Struct)
				if !ok {
					ctx.nope(t.Obj(), "type with embedded method should be a struct")
				}
				field := structType.Field(index[0])
				var fieldType types.Type = types.NewPointer(field.Type())
				var fieldExpr glang.Expr = glang.NewCallExpr(
					glang.VerbatimExpr("StructFieldRef"),
					glang.VerbatimExpr(ty),
					glang.StringLiteral{Value: field.Name()},
					glang.IdentExpr("$r"),
				)
				if _, fieldIsPointer := field.Type().(*types.Pointer); fieldIsPointer {
					fieldExpr = glang.DerefExpr{X: fieldExpr, Ty: ctx.glangType(field, field.Type())}
					fieldType = field.Type()
				}
				if types.IsInterface(fieldType.(*types.Pointer).Elem()) {
					fieldType = fieldType.(*types.Pointer).Elem()
					fieldExpr = glang.DerefExpr{X: fieldExpr, Ty: ctx.glangType(field, fieldType)}
				}
				impl = glang.FuncLit{
					Args: []glang.Binder{{Name: "$r"}},
					Body: glang.NewCallExpr(glang.VerbatimExpr("MethodResolve"),
						ctx.glangType(field, fieldType), glang.StringLiteral{Value: methodName}, fieldExpr),
				}.LeanVal()
			}
			add("ptr_"+methodName+"_unfold",
				leanForall(goBinders, fmt.Sprintf("MethodUnfold %s %s %s", ptrTy, glang.LeanStringLit(methodName), lparenS(impl))))
		}
	}

	return typeAssumptionsDecl{
		VerbatimDecl: glang.VerbatimDecl{Content: leanClass(glang.LeanEncodedName(typeName+"_Assumptions"), " [GooseExts] "+leanClassParams, fields)},
		fields:       len(fields),
	}
}

// leanMethodSet is a method set as `go.MethodSetIs` takes it: a list of entries
// `(id, some sig)`, or `(id, none)` for a signature goose does not support
// (methodSigLean), in the order of types.MethodSet (by id).
func (ctx *Ctx) leanMethodSet(n locatable, mset *types.MethodSet) string {
	var entries []string
	for i := range mset.Len() {
		sel := mset.At(i)
		sig := "none"
		if s, ok := ctx.methodSigLean(n, sel.Type().(*types.Signature)); ok {
			sig = "(some " + s + ")"
		}
		entries = append(entries, fmt.Sprintf("(%s, %s)", glang.LeanStringLit(sel.Obj().Id()), sig))
	}
	return "[" + strings.Join(entries, ", ") + "]"
}

// methodSigLean is the signature of a method of a method set as a Lean term
// (nameableSignature: a method that is not translated may mention types this
// translation cannot name), if goose supports its types.
func (ctx *Ctx) methodSigLean(n locatable, sig *types.Signature) (s string, ok bool) {
	defer func() {
		if r := recover(); r != nil {
			if _, isGooseErr := r.(gooseError); !isGooseErr {
				panic(r)
			}
			s, ok = "", false
		}
	}()
	return glang.LeanTermOf(ctx.nameableSignature(n, sig)), true
}

// typeNameable reports whether every named type t mentions is predeclared, of
// this package or of an imported package, and every alias it mentions is the
// universe's or one this package translates.
func (ctx *Ctx) typeNameable(t types.Type, seen map[types.Type]bool) bool {
	if seen[t] {
		return true
	}
	seen[t] = true
	all := func(ts ...types.Type) bool {
		for _, t := range ts {
			if !ctx.typeNameable(t, seen) {
				return false
			}
		}
		return true
	}
	vars := func(tup *types.Tuple) bool {
		for i := range tup.Len() {
			if !ctx.typeNameable(tup.At(i).Type(), seen) {
				return false
			}
		}
		return true
	}
	named := func(pkg *types.Package, args *types.TypeList) bool {
		if pkg != nil && pkg.Path() != ctx.pkgPath {
			if _, ok := ctx.importNames[pkg.Path()]; !ok {
				return false
			}
		}
		for i := range args.Len() {
			if !ctx.typeNameable(args.At(i), seen) {
				return false
			}
		}
		return true
	}
	switch t := t.(type) {
	case *types.Basic, *types.TypeParam:
		return true
	case *types.Named:
		return named(t.Obj().Pkg(), t.TypeArgs())
	case *types.Alias:
		// an alias that is not translated is declared as an axiom without a
		// descriptor (`axiom A : go.GoType`), which glangType cannot name: only
		// the universe's aliases (any) and this package's translated ones
		if pkg := t.Obj().Pkg(); pkg != nil &&
			(pkg.Path() != ctx.pkgPath || ctx.filter.GetAction(t.Obj().Name()) != declfilter.Translate) {
			return false
		}
		return named(t.Obj().Pkg(), t.TypeArgs())
	case *types.Pointer:
		return all(t.Elem())
	case *types.Slice:
		return all(t.Elem())
	case *types.Array:
		return all(t.Elem())
	case *types.Map:
		return all(t.Key(), t.Elem())
	case *types.Chan:
		return all(t.Elem())
	case *types.Signature:
		return vars(t.Params()) && vars(t.Results())
	case *types.Struct:
		for i := range t.NumFields() {
			if !ctx.typeNameable(t.Field(i).Type(), seen) {
				return false
			}
		}
		return true
	case *types.Interface:
		for i := range t.NumMethods() {
			if !ctx.typeNameable(t.Method(i).Type(), seen) {
				return false
			}
		}
		for i := range t.NumEmbeddeds() {
			if !ctx.typeNameable(t.EmbeddedType(i), seen) {
				return false
			}
		}
		return true
	case *types.Union:
		for i := range t.Len() {
			if !ctx.typeNameable(t.Term(i).Type(), seen) {
				return false
			}
		}
		return true
	}
	return false
}

func lparenS(s string) string {
	if strings.HasPrefix(s, "(") || !strings.ContainsAny(s, " \n") {
		return s
	}
	return "(" + s + ")"
}

// toLeanType is the Lean type modeling the values of a Go type
func (ctx *Ctx) toLeanType(l locatable, t types.Type) string {
	return ctx.toLeanTypeP(l, t, false)
}

// toLeanTypeP is toLeanType, where type parameters T are translated to T' if
// primed is true (in contexts where T is the go.type and T' the Lean type).
func (ctx *Ctx) toLeanTypeP(l locatable, t types.Type, primed bool) string {
	switch t := types.Unalias(t).(type) {
	case *types.Basic:
		return ctx.basicLeanType(l, t)
	case *types.Slice:
		return "GoSlice"
	case *types.Array:
		return fmt.Sprintf("(GoArray %s %d)", ctx.toLeanTypeP(l, t.Elem(), primed), t.Len())
	case *types.Pointer:
		return "Loc"
	case *types.Signature:
		return "GoFunc"
	case *types.Interface:
		return "GoInterface"
	case *types.Map:
		return "GoMap"
	case *types.Chan:
		return "GoChan"
	case *types.Named:
		var baseName string
		pkg := t.Obj().Pkg()
		if pkg == nil {
			// universe types (error) are modeled by the framework
			baseName = glang.LeanUniverseType(t.Obj().Name())
		} else if pkg.Path() != ctx.pkgPath {
			baseName = glang.LeanQuote(ctx.pkgRef(pkg)) + "." + glang.LeanIdent(t.Obj().Name())
		} else {
			baseName = glang.LeanIdent(t.Obj().Name())
		}
		if t.TypeParams() != nil {
			var params []string
			for i := 0; i < t.TypeArgs().Len(); i++ {
				params = append(params, ctx.toLeanTypeP(l, t.TypeArgs().At(i), primed))
			}
			return fmt.Sprintf("(%s %s)", baseName, strings.Join(params, " "))
		}
		return baseName
	case *types.TypeParam:
		if primed {
			return glang.LeanIdent(t.String() + "'")
		}
		return glang.LeanIdent(t.String())
	case *types.Struct:
		if t.NumFields() == 0 {
			return "Unit"
		}
		ctx.unsupported(l, "Anonymous structs with fields are not supported %s", t.String())
	}
	ctx.unsupported(l, "Unknown type %s (of type %T)", t, t)
	return ""
}

// leanPackagePropClass is the package-level Assumptions class (see
// packagePropClass).
func (ctx *Ctx) leanPackagePropClass(typeSpecs []*ast.TypeSpec) string {
	var fields []leanClassField
	for _, t := range typeSpecs {
		fields = append(fields, leanClassField{name: t.Name.Name + "_instance",
			ty: glang.LeanEncodedName(t.Name.Name + "_Assumptions")})
	}
	for _, f := range ctx.functions {
		name := ctx.funcDeclName(f)
		if ctx.filter.GetAction(name) == declfilter.Axiomatize {
			continue
		}
		var params []string
		if f.Type.TypeParams != nil {
			for _, p := range f.Type.TypeParams.List {
				for _, name := range p.Names {
					params = append(params, name.Name)
				}
			}
		}
		var typeArgs []string
		for _, p := range params {
			typeArgs = append(typeArgs, glang.LeanIdent(p))
		}
		impl := leanApplied(glang.LeanIdent(glang.FuncImpl(name)), params)
		fields = append(fields, leanClassField{name: name + "_unfold",
			ty: leanForall(leanTypeParamBinders(params, "go.GoType"),
				fmt.Sprintf("FuncUnfold %s [%s] %s", glang.LeanIdent(name),
					strings.Join(typeArgs, ", "), impl))})
	}
	for _, impName := range ctx.importNamesOrdered {
		pkg := impName.Imported()
		fields = append(fields, leanClassField{name: ctx.importAssumptionName(pkg),
			ty: glang.LeanQuote(ctx.pkgRef(pkg) + ".Assumptions")})
	}
	return leanClass("Assumptions", " [GooseExts] "+leanClassParams, fields)
}

func (ctx *Ctx) leanInfoInstance() string {
	var imps []string
	for _, impName := range ctx.importNamesOrdered {
		imps = append(imps, glang.LeanPkgId(impName.Imported().Path()))
	}
	return fmt.Sprintf("noncomputable instance info' : PkgInfo %s where\n  pkgImportedPkgs := [%s]",
		ctx.pkgIdent, strings.Join(imps, ", "))
}
