package goose

import (
	"fmt"
	"go/ast"
	"go/types"
	"math/big"
	"slices"
	"strings"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/glang"
)

// this file has the translations for types themselves
func (ctx *Ctx) typeDecl(spec *ast.TypeSpec) {
	typeName := spec.Name.Name

	if namedType, ok := ctx.typeOf(spec.Name).(*types.Named); ok {
		ctx.namedTypeSpecs = append(ctx.namedTypeSpecs, spec)

		var typeParams []string
		var typeParamsList glang.ListExpr
		if tps := namedType.TypeParams(); tps != nil {
			for i := range tps.Len() {
				typeParams = append(typeParams, tps.At(i).Obj().Name())
				typeParamsList = append(typeParamsList, glang.GallinaIdent(tps.At(i).Obj().Name()))
			}
		}
		ctx.out.typeNamedDecls = append(ctx.out.typeNamedDecls, glang.TypeDecl{
			Name: typeName,
			Body: glang.NewCallExpr(glang.VerbatimExpr("go.Named"),
				glang.StringLiteral{Value: namedType.Obj().Pkg().Path() + "." + namedType.Obj().Name()},
				typeParamsList,
			),
			TypeParams: typeParams,
		})
		// This is a performance optimization for Rocq. TC Search for
		// typeclasses involving this go.type will attempt to unify the actual
		// TC goal with the pattern for each and every declared instance (i.e.
		// TC search is linear in the number of instances), and having
		// transparent `go.Named "some_long_string"` results in slow
		// unification.
		ctx.out.typeNamedDecls = append(ctx.out.typeNamedDecls,
			glang.VerbatimDecl{Content: fmt.Sprintf("#[global] Opaque %s.", glang.ToIdent(typeName))},
		)
	}

	switch ctx.filter.GetAction(spec.Name.Name) {
	case declfilter.Axiomatize:
		typ := ctx.typeOf(spec.Name)
		var tps *types.TypeParamList
		if alias, ok := typ.(*types.Alias); ok {
			tps = alias.TypeParams()
		} else if named, ok := typ.(*types.Named); ok {
			tps = named.TypeParams()
		}

		typeStr := "go.type"
		if tps != nil && tps.Len() > 0 {
			var params []string
			for i := 0; i < tps.Len(); i++ {
				params = append(params, tps.At(i).Obj().Name())
			}
			typeStr = fmt.Sprintf("∀ (%s : go.type), go.type", strings.Join(params, " "))
		}

		if _, ok := typ.(*types.Alias); ok {
			ctx.out.typeAliasDecls = append(ctx.out.typeAliasDecls, glang.AxiomDecl{
				DeclName: typeName,
				Type:     glang.VerbatimExpr(typeStr),
			})
		} else if _, ok := typ.(*types.Named); ok {
			ctx.out.typeAliasDecls = append(ctx.out.typeAliasDecls, glang.AxiomDecl{
				DeclName: glang.ToIdent(typeName) + "ⁱᵐᵖˡ",
				Type:     glang.VerbatimExpr(typeStr),
			})
		}
		return
	case declfilter.Translate:
		if aliasedType, ok := ctx.typeOf(spec.Name).(*types.Alias); ok {
			var typeParams []string
			if tps := aliasedType.TypeParams(); tps != nil {
				for i := range tps.Len() {
					typeParams = append(typeParams, tps.At(i).Obj().Name())
				}
			}
			ctx.out.typeAliasDecls = append(ctx.out.typeAliasDecls, glang.TypeDecl{
				Name:       typeName,
				Body:       ctx.glangType(spec.Type, types.Unalias(aliasedType)),
				TypeParams: typeParams,
			})
		}
	case declfilter.Trust:
	}
}

func (ctx *Ctx) namedTypeSemanticsDecl(spec *ast.TypeSpec) []glang.Decl {
	return slices.Concat(ctx.namedRocqTypeDecl(spec), ctx.namedTypeImplDecl(spec),
		ctx.namedTypePropClassDecl(spec))
}

func fieldName(i int, s string) string {
	if s == "_" {
		return s + fmt.Sprint(i)
	}
	return s
}

// Adding a "'" to avoid conflicting with Coq keywords and definitions that
// would already be in context (like `t`). Could do this only when there is a
// conflict, but it's lower entropy to do it always rather than pick and
// choosing when.
func recordProjection(i int, s string) string {
	return fieldName(i, s) + "'"
}

func (ctx *Ctx) namedRocqTypeDecl(spec *ast.TypeSpec) (decls []glang.Decl) {
	w := new(strings.Builder)
	fmt.Fprintf(w, "Module %s.\n", glang.ToIdent(spec.Name.Name))
	fmt.Fprintf(w, "Section def.\nContext {ext : ffi_syntax} {go_gctx : GoGlobalContext}.\n")
	namedType := ctx.typeOf(spec.Name).(*types.Named)

	switch ctx.filter.GetAction(spec.Name.Name) {
	case declfilter.Trust:
		return
	case declfilter.Axiomatize:
		fmt.Fprintf(w, "Axiom t : ")
		if tps := namedType.TypeParams(); tps != nil {
			fmt.Fprintf(w, "∀ (")
			for i := range tps.Len() {
				fmt.Fprintf(w, "%s ", tps.At(i).Obj().Name())
			}
			fmt.Fprint(w, ": Type), ")
		}
		fmt.Fprintf(w, "Type.")
		// ZeroVal instance
		fmt.Fprintf(w, "\nAxiom zero_val : ")
		if tps := namedType.TypeParams(); tps != nil {
			fmt.Fprintf(w, "∀")
			for i := range tps.Len() {
				fmt.Fprintf(w, " `{!ZeroVal %s}", tps.At(i).Obj().Name())
			}
			fmt.Fprintf(w, ", ")
		}
		// FIXME: params.
		fmt.Fprintf(w, "ZeroVal ")
		if tps := namedType.TypeParams(); tps != nil {
			fmt.Fprintf(w, "(t")
			for i := range tps.Len() {
				fmt.Fprintf(w, " %s", tps.At(i).Obj().Name())
			}
			fmt.Fprintf(w, ")")
		} else {
			fmt.Fprintf(w, "t")
		}
		fmt.Fprintf(w, ".")
		fmt.Fprintf(w, "\n#[global] Existing Instance zero_val.")

		fmt.Fprint(w, "\nEnd def.")
		fmt.Fprintf(w, "\nEnd %s.", glang.ToIdent(spec.Name.Name))
	case declfilter.Translate:
		switch t := ctx.typeOf(spec.Type).(type) {
		case *types.Struct:
			fmt.Fprintf(w, "Record t")

			if tps := namedType.TypeParams(); tps != nil {
				fmt.Fprintf(w, " {")
				for i := range tps.Len() {
					fmt.Fprintf(w, "%s ", tps.At(i).Obj().Name())
				}
				fmt.Fprint(w, ": Type}")
			}
			fmt.Fprintf(w, " :=\nmk {\n")

			for i := range t.NumFields() {
				f := t.Field(i)
				ft := ctx.toGallinaType(spec, f.Type())
				fmt.Fprintf(w, "  %s : %s;\n", recordProjection(i, f.Name()), ft)
			}
			fmt.Fprintf(w, "}.\n")

			// ZeroVal instance
			fmt.Fprintf(w, "\n#[global] Instance zero_val")
			if tps := namedType.TypeParams(); tps != nil {
				for i := range tps.Len() {
					fmt.Fprintf(w, " `{!ZeroVal %s}", tps.At(i).Obj().Name())
				}
			}
			fmt.Fprintf(w, " : ZeroVal t := {| zero_val := mk")

			if tps := namedType.TypeParams(); tps != nil {
				for i := range tps.Len() {
					fmt.Fprintf(w, " %s", tps.At(i).Obj().Name())
				}
			}
			for range t.NumFields() {
				fmt.Fprint(w, " (zero_val _)")
			}
			fmt.Fprint(w, "|}.")

			fmt.Fprint(w, "\n#[global] Arguments mk : clear implicits.")
		default:
			fmt.Fprintf(w, "Definition t")

			if tps := namedType.TypeParams(); tps != nil {
				fmt.Fprintf(w, " {")
				for i := range tps.Len() {
					fmt.Fprintf(w, "%s ", tps.At(i).Obj().Name())
				}
				fmt.Fprint(w, ": Type}")
			}
			fmt.Fprintf(w, " : Type := ")

			rocqType := ctx.toGallinaType(spec, t)
			fmt.Fprintf(w, "%s.", rocqType)
		}
		fmt.Fprint(w, "\n#[global] Arguments t : clear implicits.")
		fmt.Fprint(w, "\nEnd def.")
		fmt.Fprintf(w, "\nEnd %s.", glang.ToIdent(spec.Name.Name))
	}

	recordDecl := glang.VerbatimDecl{
		Content: w.String(),
	}
	decls = append(decls, recordDecl)
	return decls
}

func (ctx *Ctx) namedTypeImplDecl(spec *ast.TypeSpec) (decls []glang.Decl) {
	if ctx.filter.GetAction(spec.Name.Name) != declfilter.Translate {
		return nil
	}
	typeName := spec.Name.Name
	gallinaTypeName := glang.ToIdent(typeName)

	var body glang.Expr
	if s, ok := ctx.typeOf(spec.Type).(*types.Struct); ok {
		ty := ctx.structType(s)
		w := new(strings.Builder)
		typeParams := ""
		typeArgs := ""
		for _, t := range ctx.typeParamList(spec.TypeParams) {
			typeParams += fmt.Sprintf(" (%s : go.type)", t)
			typeArgs += fmt.Sprintf(" %s", t)
		}

		body = glang.VerbatimExpr(fmt.Sprintf("go.StructType (%s'fds%s)",
			spec.Name.Name, typeArgs))

		fmt.Fprintf(w, "Definition %s'fds_unsealed%s {ext : ffi_syntax} {go_gctx : GoGlobalContext} : list go.field_decl := [\n%s\n].", spec.Name.Name, typeParams, ty.CoqFields(2))
		fmt.Fprintf(w, "\nProgram Definition %s'fds%s {ext : ffi_syntax} {go_gctx : GoGlobalContext} := sealed (%s'fds_unsealed%s).", spec.Name.Name, typeParams, spec.Name.Name, typeArgs)

		fmt.Fprintf(w, "\nGlobal Instance equals_unfold_%[1]s%[2]s {ext : ffi_syntax} {go_gctx : GoGlobalContext} : %[1]s'fds%[2]s =→ %[1]s'fds_unsealed%[2]s.",
			spec.Name.Name, typeArgs)
		fmt.Fprintf(w, "\nProof. rewrite /%s'fds seal_eq //. Qed.", spec.Name.Name)

		decl := glang.VerbatimDecl{Content: w.String()}
		decls = append(decls, decl)
	} else {
		body = ctx.glangType(spec, ctx.typeOf(spec.Type))
	}

	decl := glang.TypeDecl{
		Name:       gallinaTypeName + "ⁱᵐᵖˡ",
		Body:       body,
		TypeParams: ctx.typeParamList(spec.TypeParams),
	}
	decls = append(decls, decl)
	return decls
}

func (ctx *Ctx) namedTypePropClassDecl(spec *ast.TypeSpec) []glang.Decl {
	typeName := spec.Name.Name
	gallinaTypeName := glang.ToIdent(typeName)
	gallinaImplTypeName := glang.ToIdent(typeName) + "ⁱᵐᵖˡ"

	t := ctx.typeOf(spec.Name).(*types.Named)
	tunder := ctx.typeOf(spec.Type)

	typeParams := ""
	if t.TypeParams() != nil {
		for i := range t.TypeParams().Len() {
			name := t.TypeParams().At(i).Obj().Name()
			typeParams += " " + name
		}
	}

	w := new(strings.Builder)
	fmt.Fprintln(w, "Class "+typeName+"_Assumptions "+
		"{ext : ffi_syntax} `{!GoGlobalContext} `{!GoLocalContext} `{!GoSemanticsFunctions} : Prop :=")
	fmt.Fprintln(w, "{")

	// type repr instance
	if _, ok := ctx.typeOf(spec.Type).(*types.Struct); ok ||
		ctx.filter.GetAction(typeName) == declfilter.Axiomatize {
		fmt.Fprintf(w, "  #[global] %s_type_repr ", typeName)
		if t.TypeParams() != nil {
			for i := range t.TypeParams().Len() {
				fmt.Fprintf(w, "%s %[1]s' `{!ZeroVal %[1]s'} `{!TypeRepr %[1]s %[1]s'}", t.TypeParams().At(i).Obj().Name())
			}
		}
		fmt.Fprintf(w, " :: go.TypeReprUnderlying ")
		if t.TypeParams() != nil {
			fmt.Fprintf(w, "(%s", gallinaImplTypeName)
			for i := range t.TypeParams().Len() {
				fmt.Fprintf(w, " %s", t.TypeParams().At(i).Obj().Name())
			}
			fmt.Fprintf(w, ") (%s.t", gallinaTypeName)

			for i := range t.TypeParams().Len() {
				fmt.Fprintf(w, " %s'", t.TypeParams().At(i).Obj().Name())
			}
			fmt.Fprintf(w, ");\n")
		} else {
			fmt.Fprintf(w, "%s %s.t;\n", gallinaImplTypeName, gallinaTypeName)
		}
	}

	// underlying instance
	fmt.Fprintf(w, "  #[global] %[1]s_underlying%[2]s :: (%[3]s%[2]s) <u (%[4]s%[2]s);\n", typeName, typeParams, gallinaTypeName, gallinaImplTypeName)
	if ctx.filter.GetAction(typeName) == declfilter.Axiomatize {
		fmt.Fprintf(w, "  #[global] %[1]s_underlying%[2]s :: (%[1]s%[2]s) ↓u (%[1]s%[2]s);\n", gallinaImplTypeName, typeParams)
	}

	// maybe emit StructFieldSet and StructFieldGet instances
	if ctx.filter.GetAction(t.Obj().Name()) == declfilter.Translate {
		if st, ok := tunder.(*types.Struct); ok {
			rocqTypeParams := ""
			if t.TypeParams() != nil {
				for i := range t.TypeParams().Len() {
					rocqTypeParams += " " + t.TypeParams().At(i).Obj().Name() + "'"
				}
			}

			for i := range st.NumFields() {
				fieldName := fieldName(i, st.Field(i).Name())
				projName := recordProjection(i, st.Field(i).Name())

				fmt.Fprintf(w, "  #[global] %s_get_%s%s%s ", typeName, fieldName, typeParams, rocqTypeParams)
				fmt.Fprintf(w, "(x : %[1]s.t%[2]s) :: "+
					"⟦StructFieldGet (%[3]s%[4]s) \"%[5]s\", #x⟧ ⤳[under] #x.(%[1]s.%[6]s);\n",
					gallinaTypeName, rocqTypeParams, gallinaImplTypeName, typeParams, fieldName, projName)

				fmt.Fprintf(w, "  #[global] %s_set_%s%s%s ", typeName, fieldName, typeParams, rocqTypeParams)
				fmt.Fprintf(w, "(x : %[1]s.t%[2]s) y :: "+
					"⟦StructFieldSet (%[3]s%[4]s) \"%[5]s\", (#x, #y)⟧ ⤳[under] #(x <|%[1]s.%[6]s := y|>);\n",
					gallinaTypeName, rocqTypeParams, gallinaImplTypeName, typeParams, fieldName, projName)
			}
		}
	}

	ty := "(" + gallinaTypeName + typeParams + ")"
	ptrTy := "(go.PointerType " + ty + ")"

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
				impl = "(" + glang.TypeMethod(typeName, methodName) + typeParams + ")"
			} else {
				structType, ok := t.Underlying().(*types.Struct)
				if !ok {
					ctx.nope(t.Obj(), "type with embedded method should be a struct")
				}
				field := structType.Field(index[0])
				impl = `(λ: "$r", MethodResolve ` + ctx.glangType(field, field.Type()).Coq(true) + ` "` +
					methodName + `" (StructFieldGet ` + ty + ` "` + field.Name() + `" "$r" ))%V`
			}
			fmt.Fprintln(w, "  #[global] "+typeName+"_"+methodName+"_unfold"+typeParams+
				" :: MethodUnfold "+ty+` "`+methodName+`" `+impl+";")
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
					impl = "(" + glang.TypeMethod(typeName, methodName) + typeParams + ")"
				} else {
					impl = `(λ: "$r", MethodResolve ` + ty + ` "` +
						methodName + `" (![` + ty + `] "$r"))`
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

				// if `&(x.f)` would be a `**T`, dereference it to get `*T`
				if _, fieldIsPointer := field.Type().(*types.Pointer); fieldIsPointer {
					fieldExpr = glang.DerefExpr{
						X:  fieldExpr,
						Ty: ctx.glangType(field, field.Type()),
					}
					fieldType = field.Type()
				}

				if types.IsInterface(fieldType.(*types.Pointer).Elem()) {
					fieldType = fieldType.(*types.Pointer).Elem()
					fieldExpr = glang.DerefExpr{
						X:  fieldExpr,
						Ty: ctx.glangType(field, fieldType),
					}
				}

				impl = `(λ: "$r", MethodResolve ` + ctx.glangType(field, fieldType).Coq(true) + ` "` +
					methodName + `" ` + fieldExpr.Coq(true) + ")"
			}
			fmt.Fprintln(w, "  #[global] "+typeName+"'ptr_"+methodName+"_unfold"+typeParams+
				" :: MethodUnfold "+ptrTy+` "`+methodName+`" `+impl+";")
		}
	}
	fmt.Fprint(w, "}.")

	decl := glang.VerbatimDecl{
		Content: w.String(),
	}

	return []glang.Decl{decl}
}

func (ctx *Ctx) typeOf(e ast.Expr) types.Type {
	return ctx.info.TypeOf(e)
}

func (ctx *Ctx) structType(t *types.Struct) glang.StructType {
	ty := glang.StructType{}
	for i := range t.NumFields() {
		fieldType := t.Field(i).Type()
		fieldName := fieldName(i, t.Field(i).Name())

		ty.Fields = append(ty.Fields, glang.FieldDecl{
			Name:     fieldName,
			Type:     ctx.glangType(t.Field(i), fieldType),
			Embedded: t.Field(i).Embedded(),
		})
	}
	return ty
}

func (ctx *Ctx) basicType(t *types.Basic) glang.Expr {
	if after, ok := strings.CutPrefix(t.Name(), "untyped "); ok {
		return glang.GallinaIdent("go.untyped_" + after)
	}
	switch t.Name() {
	case "Pointer":
		return glang.GallinaIdent("unsafe.Pointer")
	}
	return glang.GallinaIdent("go." + t.Name())
}

func (ctx *Ctx) signature(n locatable, t *types.Signature) glang.Expr {
	var argTypes glang.ListExpr
	var variadic glang.Expr
	var resultTypes glang.ListExpr

	// Ignore Recv; this might be a signature in an interface.

	if t.Params() != nil {
		for i := range t.Params().Len() {
			argTypes = append(argTypes, ctx.glangType(n, t.Params().At(i).Type()))
		}
	}
	variadic = glang.BoolLiteral(t.Variadic())
	if t.Results() != nil {
		for i := range t.Results().Len() {
			resultTypes = append(resultTypes, ctx.glangType(n, t.Results().At(i).Type()))
		}
	}
	return glang.NewCallExpr(glang.GallinaIdent("go.Signature"),
		argTypes,
		variadic,
		resultTypes,
	)
}

func (ctx *Ctx) interfaceType(n locatable, t *types.Interface) glang.Expr {
	var elems glang.ListExpr
	for i := range t.NumExplicitMethods() {
		elems = append(elems,
			glang.NewCallExpr(glang.GallinaIdent("go.MethodElem"),
				glang.StringLiteral{Value: t.ExplicitMethod(i).Name()},
				ctx.signature(n, t.ExplicitMethod(i).Signature())),
		)
	}
	for i := range t.NumEmbeddeds() {
		em := t.EmbeddedType(i)
		var terms glang.ListExpr
		if uem, ok := em.(*types.Union); ok {
			for j := range uem.Len() {
				typeTermCons := "go.TypeTerm"
				if uem.Term(j).Tilde() {
					typeTermCons = typeTermCons + "Underlying"
				}
				terms = append(terms, glang.NewCallExpr(
					glang.GallinaIdent(typeTermCons),
					ctx.glangType(n, uem.Term(j).Type())),
				)
			}
		} else {
			terms = append(terms, glang.NewCallExpr(
				glang.GallinaIdent("go.TypeTerm"),
				ctx.glangType(n, em)),
			)
		}
		elems = append(elems,
			glang.NewCallExpr(glang.GallinaIdent("go.TypeElem"), terms))
	}

	return glang.NewCallExpr(glang.GallinaIdent("go.InterfaceType"), elems)
}

func (ctx *Ctx) glangType(n locatable, t types.Type) glang.Expr {
	switch t := t.(type) {
	case *types.Struct:
		return ctx.structType(t)
	case *types.TypeParam:
		return glang.GallinaIdent(t.Obj().Name())
	case *types.Basic:
		return ctx.basicType(t)
	case *types.Pointer:
		return glang.NewCallExpr(glang.VerbatimExpr("go.PointerType"), ctx.glangType(n, t.Elem()))
	case *types.Named:
		if t.Obj().Pkg() == nil {
			switch t.Obj().Name() {
			case "error", "any", "comparable":
				return glang.GallinaIdent("go." + t.Obj().Name())
			}
			ctx.nope(n, "unexpected built-in type %v", t.Obj())
		}
		if t.TypeArgs().Len() != 0 {
			return glang.CallExpr{
				MethodName: glang.GallinaIdent(ctx.qualifiedName(t.Obj())),
				Args:       ctx.convertTypeArgsToGlang(n, t.TypeArgs()),
			}
		} else {
			return glang.GallinaIdent(ctx.qualifiedName(t.Obj()))
		}
	case *types.Alias:
		if t.Obj().Pkg() == nil {
			switch t.Obj().Name() {
			case "error", "any", "comparable":
				return glang.GallinaIdent("go." + t.Obj().Name())
			}
			ctx.nope(n, "unexpected built-in type %v", t.Obj())
		}
		if t.TypeArgs().Len() != 0 {
			return glang.CallExpr{
				MethodName: glang.GallinaIdent(ctx.qualifiedName(t.Obj())),
				Args:       ctx.convertTypeArgsToGlang(n, t.TypeArgs()),
			}
		} else {
			return glang.GallinaIdent(ctx.qualifiedName(t.Obj()))
		}

	case *types.Map:
		return glang.NewCallExpr(glang.GallinaIdent("go.MapType"),
			ctx.glangType(n, t.Key()), ctx.glangType(n, t.Elem()))
	case *types.Chan:
		chanDir := ""
		switch t.Dir() {
		case types.SendRecv:
			chanDir = "go.sendrecv"
		case types.SendOnly:
			chanDir = "go.sendonly"
		case types.RecvOnly:
			chanDir = "go.recvonly"
		}
		return glang.NewCallExpr(glang.GallinaIdent("go.ChannelType"),
			glang.GallinaIdent(chanDir), ctx.glangType(n, t.Elem()),
		)
	case *types.Array:
		return glang.NewCallExpr(glang.VerbatimExpr("go.ArrayType"),
			glang.ZLiteral{Value: big.NewInt(t.Len())}, ctx.glangType(n, t.Elem()))
	case *types.Signature:
		return glang.NewCallExpr(glang.GallinaIdent("go.FunctionType"), ctx.signature(n, t))
	case *types.Interface:
		return ctx.interfaceType(n, t)
	case *types.Slice:
		return glang.NewCallExpr(glang.GallinaIdent("go.SliceType"), ctx.glangType(n, t.Elem()))
	}
	ctx.unsupported(n, "unknown type %v, %T", t, t)
	return nil // unreachable
}

func sliceElem(t types.Type) types.Type {
	if t, ok := underlyingType(t).(*types.Slice); ok {
		return t.Elem()
	}
	panic(fmt.Errorf("expected slice type, got %v", t))
}

func ptrElem(t types.Type) types.Type {
	if t, ok := underlyingType(t).(*types.Pointer); ok {
		return t.Elem()
	}
	panic(fmt.Errorf("expected pointer type, got %v", t))
}

func chanElem(t types.Type) types.Type {
	if t, ok := underlyingType(t).(*types.Chan); ok {
		return t.Elem()
	}
	panic(fmt.Errorf("expected channel type, got %v", t))
}

func (ctx *Ctx) convertTypeArgsToGlang(l locatable, typeList *types.TypeList) (glangTypeArgs []glang.Expr) {
	glangTypeArgs = make([]glang.Expr, typeList.Len())
	for i := range glangTypeArgs {
		glangTypeArgs[i] = ctx.glangType(l, typeList.At(i))
	}
	return
}

type structTypeInfo struct {
	name           string
	throughPointer bool
	namedType      *types.Named
	structType     *types.Struct
	typeArgs       *types.TypeList
}

func (ctx *Ctx) structInfoToGlangType(info structTypeInfo) glang.Expr {
	return glang.GallinaIdent(info.name)
}

func (ctx *Ctx) getStructInfo(t types.Type) (structTypeInfo, bool) {
	throughPointer := false
	if pt, ok := t.(*types.Pointer); ok {
		throughPointer = true
		t = pt.Elem()
	}
	if t, ok := t.(*types.Named); ok {
		name := ctx.qualifiedName(t.Obj())
		if structType, ok := t.Underlying().(*types.Struct); ok {
			return structTypeInfo{
				name:           name,
				typeArgs:       t.TypeArgs(),
				namedType:      t,
				throughPointer: throughPointer,
				structType:     structType,
			}, true
		}
	}
	return structTypeInfo{}, false
}

func (ctx *Ctx) basicTypeToGallina(n locatable, t *types.Basic) string {
	switch t.Name() {
	case "uint64", "int64":
		return "w64"
	case "uint32", "int32":
		return "w32"
	case "uint16", "int16":
		return "w16"
	case "uint8", "int8", "byte":
		return "w8"
	case "uint", "int":
		return "w64"
	case "float64":
		return "w64"
	case "float32":
		return "w32"
	case "bool":
		return "bool"
	case "string", "untyped string":
		return "go_string"
	case "Pointer", "uintptr":
		return "loc"
	}
	ctx.unsupported(n, "Unknown basic type %s,", t.Name())
	return ""
}

func (ctx *Ctx) namedTypeToGallina(l locatable, t *types.Named) string {
	var baseName string
	pkg := t.Obj().Pkg()
	if pkg != nil {
		baseName = pkg.Name() + "." + glang.ToIdent(t.Obj().Name()) + ".t"
	} else {
		baseName = glang.ToIdent(t.Obj().Name()) + ".t"
	}
	// if TypeParams() is not nil, there are type parameters in the base named type
	if t.TypeParams() != nil {
		var params []string
		for i := 0; i < t.TypeArgs().Len(); i++ {
			params = append(params, ctx.toGallinaType(l, t.TypeArgs().At(i)))
		}
		return fmt.Sprintf("(%s %s)", baseName, strings.Join(params, " "))
	}
	return baseName
}

// ToCoqType converts a type to a Gallina type modeling that type
func (ctx *Ctx) toGallinaType(l locatable, t types.Type) string {
	switch t := types.Unalias(t).(type) {
	case *types.Basic:
		return ctx.basicTypeToGallina(l, t)
	case *types.Slice:
		return "slice.t"
	case *types.Array:
		return fmt.Sprintf("(array.t %s %d)", ctx.toGallinaType(l, t.Elem()), t.Len())
	case *types.Pointer:
		return "loc"
	case *types.Signature:
		return "func.t"
	case *types.Interface:
		return "interface.t"
	case *types.Map:
		return "map.t"
	case *types.Chan:
		return "chan.t"
	case *types.Named:
		return ctx.namedTypeToGallina(l, t)
	case *types.TypeParam:
		return t.String()
	case *types.Struct:
		if t.NumFields() == 0 {
			return "unit"
		}
		ctx.unsupported(l, "Anonymous structs with fields are not supported %s", t.String())
	}
	ctx.unsupported(l, "Unknown type %s (of type %T)", t, t)
	return ""
}
