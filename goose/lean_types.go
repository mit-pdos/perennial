package goose

// Lean versions of the declarations that the Rocq backend emits as verbatim
// text (see types.go and goose.go).

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
	fmt.Fprintf(w, "class %s%s : Prop", glang.LeanQuoteComponent(name), params)
	if len(fields) == 0 {
		return w.String()
	}
	fmt.Fprint(w, " where")
	var names []string
	for _, f := range fields {
		fname := glang.LeanQuoteComponent(f.name)
		fmt.Fprintf(w, "\n  %s : %s", fname, f.ty)
		names = append(names, glang.LeanQuoteComponent(name)+"."+fname)
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

// namedLeanTypeDecl is the Lean version of namedRocqTypeDecl: the Lean type
// modeling values of the Go named type, in a namespace named after the type.
func (ctx *Ctx) namedLeanTypeDecl(spec *ast.TypeSpec) string {
	w := new(strings.Builder)
	ns := glang.LeanIdent(spec.Name.Name)
	fmt.Fprintf(w, "namespace %s\n", ns)
	params := ctx.namedTypeParams(spec)
	typeBinders := leanTypeParamBinders(params, "Type")
	tApplied := leanApplied("t", params)

	switch ctx.filter.GetAction(spec.Name.Name) {
	case declfilter.Axiomatize:
		fmt.Fprintf(w, "axiom t : %s\n", leanForall(typeBinders, "Type"))
		zvBinders := ""
		if len(params) > 0 {
			zvBinders = "{" + strings.TrimSuffix(strings.TrimPrefix(typeBinders, "("), ")") + "}"
			for _, p := range params {
				zvBinders += " [ZeroVal " + glang.LeanIdent(p) + "]"
			}
		}
		fmt.Fprintf(w, "axiom zero_val : %s\n", leanForall(zvBinders, "ZeroVal "+tApplied))
		fmt.Fprintf(w, "attribute [instance] zero_val\n")
	case declfilter.Translate:
		switch t := ctx.typeOf(spec.Type).(type) {
		case *types.Struct:
			sep := ""
			if typeBinders != "" {
				sep = " "
			}
			fmt.Fprintf(w, "structure t [FfiSyntax]%s%s where\n  mk ::\n", sep, typeBinders)
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
			fmt.Fprintf(w, "\ninstance zero_val [FfiSyntax]%s : ZeroVal %s :=\n  ⟨t.mk", zvBinders, tApplied)
			for range t.NumFields() {
				fmt.Fprint(w, " zeroValDef")
			}
			fmt.Fprint(w, "⟩\n")
		default:
			sep := ""
			if typeBinders != "" {
				sep = " "
			}
			fmt.Fprintf(w, "abbrev t [FfiSyntax]%s%s : Type := %s\n", sep, typeBinders, ctx.toLeanType(spec, t))
		}
	}
	fmt.Fprintf(w, "end %s", ns)
	return w.String()
}

// leanFdsDecl is the Lean version of the 'fds declarations for a struct type.
func (ctx *Ctx) leanFdsDecl(spec *ast.TypeSpec, ty glang.StructType) string {
	name := spec.Name.Name
	params := ctx.typeParamList(spec.TypeParams)
	binders := ""
	if len(params) > 0 {
		binders = " " + leanTypeParamBinders(params, "go.GoType")
	}
	fds := glang.LeanQuote(name + "'fds")
	fdsU := glang.LeanQuote(name + "'fds_unsealed")
	w := new(strings.Builder)
	fmt.Fprintf(w, "@[reducible] def %s [FfiSyntax] [GoGlobalContext]%s : List go.field_decl :=\n  %s\n", fdsU, binders,
		ty.LeanFields())
	fmt.Fprintf(w, "\n@[irreducible] def %s [FfiSyntax] [GoGlobalContext]%s : List go.field_decl :=\n  %s\n",
		fds, binders, leanApplied(fdsU, params))
	fmt.Fprintf(w, "\ninstance %s [FfiSyntax] [GoGlobalContext]%s :\n    EqualsUnfold %s %s :=\n  ⟨by unfold %s; rfl⟩",
		glang.LeanQuoteComponent("equals_unfold_"+name), binders, leanApplied(fds, params),
		leanApplied(fdsU, params), fds)
	return w.String()
}

func (ctx *Ctx) leanStructImplBody(spec *ast.TypeSpec) glang.Expr {
	var fdsArg glang.Expr = glang.GallinaIdent(spec.Name.Name + "'fds")
	params := ctx.typeParamList(spec.TypeParams)
	if len(params) > 0 {
		var args []glang.Expr
		for _, p := range params {
			args = append(args, glang.GallinaIdent(p))
		}
		fdsArg = glang.CallExpr{MethodName: fdsArg, Args: args}
	}
	return glang.CallExpr{MethodName: glang.VerbatimExpr("go.StructType"), Args: []glang.Expr{fdsArg}}
}

// namedTypeLeanPropClassDecl is the Lean version of namedTypePropClassDecl.
func (ctx *Ctx) namedTypeLeanPropClassDecl(spec *ast.TypeSpec) string {
	typeName := spec.Name.Name
	gallinaTypeName := glang.LeanIdent(typeName)
	gallinaImplTypeName := glang.LeanIdent(glang.ToIdent(typeName) + "ⁱᵐᵖˡ")

	t := ctx.typeOf(spec.Name).(*types.Named)
	tunder := ctx.typeOf(spec.Type)

	var params []string
	if t.TypeParams() != nil {
		for i := range t.TypeParams().Len() {
			params = append(params, t.TypeParams().At(i).Obj().Name())
		}
	}
	goBinders := leanTypeParamBinders(params, "go.GoType")
	rocqBinders := leanTypeParamBinders(primed(params), "Type")

	var fields []leanClassField
	add := func(name, ty string) {
		fields = append(fields, leanClassField{name: name, ty: ty})
	}

	implTy := leanApplied(gallinaImplTypeName, params)
	ty := leanApplied(gallinaTypeName, params)
	rocqTy := leanApplied(gallinaTypeName+".t", primed(params))

	// type repr instance
	if _, ok := ctx.typeOf(spec.Type).(*types.Struct); ok ||
		ctx.filter.GetAction(typeName) == declfilter.Axiomatize {
		binders := ""
		if len(params) > 0 {
			binders = goBinders + " " + rocqBinders
			for _, p := range params {
				pi, pi_ := glang.LeanIdent(p), glang.LeanIdent(p+"'")
				binders += fmt.Sprintf(" [ZeroVal %s] [TypeRepr %s %s]", pi_, pi, pi_)
			}
		}
		add(typeName+"_type_repr", leanForall(binders, fmt.Sprintf("go.TypeReprUnderlying %s %s", implTy, rocqTy)))
	}

	// underlying instance
	add(typeName+"_underlying", leanForall(goBinders, fmt.Sprintf("go.UnderlyingDirectedEq %s %s", ty, implTy)))
	if ctx.filter.GetAction(typeName) == declfilter.Axiomatize {
		add(glang.ToIdent(typeName)+"ⁱᵐᵖˡ"+"_underlying",
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
				if rocqBinders != "" {
					xBinder += " " + rocqBinders
				}
				if xBinder != "" {
					xBinder += " "
				}
				add(typeName+"_get_"+fieldName, fmt.Sprintf(
					"∀ %s(x : %s), go.IsGoStepPureDetTagged under (StructFieldGet %s %s) #x (Val #(x.%s))",
					xBinder, rocqTy, implTy, glang.LeanStringLit(fieldName), projName))
				add(typeName+"_set_"+fieldName, fmt.Sprintf(
					"∀ %s(x : %s) (y : %s), go.IsGoStepPureDetTagged under (StructFieldSet %s %s) (PairV #x #y) (Val #(({ x with %s := y } : %s)))",
					xBinder, rocqTy, fieldTy, implTy, glang.LeanStringLit(fieldName), projName, rocqTy))
			}
		}
	}

	ptrTy := "(go.GoType.PointerType " + ty + ")"

	if !types.IsInterface(t) {
		// for every method in `t`
		goMset := types.NewMethodSet(t)
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
			add(typeName+"_"+methodName+"_unfold",
				leanForall(goBinders, fmt.Sprintf("MethodUnfold %s %s %s", ty, glang.LeanStringLit(methodName), lparenS(impl))))
		}

		// for every method in `*t`
		goPtrMset := types.NewMethodSet(types.NewPointer(t))
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
					ctx.glangType(t.Obj(), t),
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
			add(typeName+"'ptr_"+methodName+"_unfold",
				leanForall(goBinders, fmt.Sprintf("MethodUnfold %s %s %s", ptrTy, glang.LeanStringLit(methodName), lparenS(impl))))
		}
	}

	return leanClass(typeName+"_Assumptions", " [FfiSyntax] "+leanClassParams, fields)
}

func lparenS(s string) string {
	if strings.HasPrefix(s, "(") || !strings.ContainsAny(s, " \n") {
		return s
	}
	return "(" + s + ")"
}

// toLeanType is the Lean version of toGallinaType
func (ctx *Ctx) toLeanType(l locatable, t types.Type) string {
	return ctx.toLeanTypeP(l, t, false)
}

// toLeanTypeP is toLeanType, where type parameters T are translated to T' if
// primed is true (in contexts where T is the go.type and T' the Lean type).
func (ctx *Ctx) toLeanTypeP(l locatable, t types.Type, primed bool) string {
	switch t := types.Unalias(t).(type) {
	case *types.Basic:
		s := ctx.basicTypeToGallina(l, t)
		if s == "bool" {
			return "Bool"
		}
		return glang.LeanRename(s)
	case *types.Slice:
		return "slice.t"
	case *types.Array:
		return fmt.Sprintf("(array.t %s %d)", ctx.toLeanTypeP(l, t.Elem(), primed), t.Len())
	case *types.Pointer:
		return "Loc"
	case *types.Signature:
		return "func.t"
	case *types.Interface:
		return "interface.t"
	case *types.Map:
		return "map.t"
	case *types.Chan:
		return "chan.t"
	case *types.Named:
		var baseName string
		pkg := t.Obj().Pkg()
		if pkg != nil && pkg.Path() != ctx.pkgPath {
			baseName = ctx.pkgRef(pkg) + "." + glang.ToIdent(t.Obj().Name()) + ".t"
		} else {
			baseName = glang.ToIdent(t.Obj().Name()) + ".t"
		}
		baseName = glang.LeanQuote(baseName)
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

// leanPackagePropClass is the Lean version of the package-level Assumptions
// class (see packagePropClass).
func (ctx *Ctx) leanPackagePropClass(typeSpecs []*ast.TypeSpec) string {
	var fields []leanClassField
	for _, t := range typeSpecs {
		fields = append(fields, leanClassField{name: t.Name.Name + "_instance",
			ty: glang.LeanQuoteComponent(t.Name.Name + "_Assumptions")})
	}
	for _, f := range ctx.functions {
		if ctx.filter.GetAction(f.Name.Name) == declfilter.Axiomatize {
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
		impl := leanApplied(glang.LeanIdent(glang.FuncImpl(f.Name.Name)), params)
		fields = append(fields, leanClassField{name: f.Name.Name + "_unfold",
			ty: leanForall(leanTypeParamBinders(params, "go.GoType"),
				fmt.Sprintf("FuncUnfold %s [%s] %s", glang.LeanIdent(f.Name.Name),
					strings.Join(typeArgs, ", "), impl))})
	}
	for _, impName := range ctx.importNamesOrdered {
		pkg := impName.Imported()
		fields = append(fields, leanClassField{name: ctx.importAssumptionName(pkg),
			ty: glang.LeanQuote(ctx.pkgRef(pkg) + ".Assumptions")})
	}
	params := " " + leanClassParams
	if ctx.declImplicitParams != "" {
		params = " [FfiSyntax]" + params
	}
	return leanClass("Assumptions", params, fields)
}

func (ctx *Ctx) leanInfoInstance() string {
	var imps []string
	for _, impName := range ctx.importNamesOrdered {
		imps = append(imps, glang.LeanPkgId(impName.Imported().Path()))
	}
	return fmt.Sprintf("instance info' : PkgInfo %s where\n  pkgImportedPkgs := [%s]",
		ctx.pkgIdent, strings.Join(imps, ", "))
}
