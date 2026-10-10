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
				typeParamsList = append(typeParamsList, glang.TermIdent(tps.At(i).Obj().Name()))
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
		// The descriptor is irreducible, so that unification against instances
		// for other types does not unfold it to `go.Named "some_long_string"`.
		ctx.out.typeNamedDecls = append(ctx.out.typeNamedDecls, glang.VerbatimDecl{
			Content: fmt.Sprintf("attribute [irreducible] %s", glang.LeanTypeDesc(typeName)),
		})
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

		var typeStr glang.Expr = glang.VerbatimExpr("go.type")
		if tps != nil && tps.Len() > 0 {
			var params []string
			for i := 0; i < tps.Len(); i++ {
				params = append(params, tps.At(i).Obj().Name())
			}
			typeStr = glang.GenericTypeExpr{Params: params}
		}

		if _, ok := typ.(*types.Alias); ok {
			// the descriptor X.ty, as for a translated alias (glang.TypeDecl)
			ctx.out.typeAliasDecls = append(ctx.out.typeAliasDecls, glang.AxiomDecl{
				DeclName: typeName + ".ty",
				Type:     typeStr,
			})
		} else if _, ok := typ.(*types.Named); ok {
			ctx.out.typeAliasDecls = append(ctx.out.typeAliasDecls, glang.AxiomDecl{
				DeclName: glang.TypeImpl(glang.ToIdent(typeName)),
				Type:     typeStr,
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
				Alias:      true,
			})
		}
	case declfilter.Trust:
	}
}

func (ctx *Ctx) namedTypeSemanticsDecl(spec *ast.TypeSpec) []glang.Decl {
	return slices.Concat(ctx.namedTypeModelDecl(spec), ctx.namedTypeImplDecl(spec),
		ctx.namedTypePropClassDecl(spec))
}

func fieldName(i int, s string) string {
	if s == "_" {
		return s + fmt.Sprint(i)
	}
	return s
}

// Adding a "'" to avoid conflicting with Lean keywords and definitions that
// would already be in context. Could do this only when there is a
// conflict, but it's lower entropy to do it always rather than pick and
// choosing when.
func recordProjection(i int, s string) string {
	return fieldName(i, s) + "'"
}

// namedTypeModelDecl declares the Lean type modeling the values of a Go named
// type (see namedLeanTypeDecl).
func (ctx *Ctx) namedTypeModelDecl(spec *ast.TypeSpec) []glang.Decl {
	if ctx.filter.GetAction(spec.Name.Name) == declfilter.Trust {
		return nil
	}
	return []glang.Decl{glang.VerbatimDecl{Content: ctx.namedLeanTypeDecl(spec)}}
}

func (ctx *Ctx) namedTypeImplDecl(spec *ast.TypeSpec) (decls []glang.Decl) {
	if ctx.filter.GetAction(spec.Name.Name) != declfilter.Translate {
		return nil
	}
	typeName := spec.Name.Name

	var body glang.Expr
	if s, ok := ctx.typeOf(spec.Type).(*types.Struct); ok {
		ty := ctx.structType(s)

		decls = append(decls, glang.VerbatimDecl{Content: ctx.leanFdsDecl(spec, ty)})
		body = ctx.leanStructImplBody(spec)
	} else {
		body = ctx.glangType(spec, ctx.typeOf(spec.Type))
	}

	decl := glang.TypeDecl{
		Name:       glang.TypeImpl(glang.ToIdent(typeName)),
		Body:       body,
		TypeParams: ctx.typeParamList(spec.TypeParams),
	}
	decls = append(decls, decl)
	return decls
}

func (ctx *Ctx) namedTypePropClassDecl(spec *ast.TypeSpec) []glang.Decl {
	return []glang.Decl{glang.VerbatimDecl{Content: ctx.namedTypeLeanPropClassDecl(spec)}}
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
		return glang.TermIdent("go.untyped_" + after)
	}
	switch t.Name() {
	case "Pointer":
		return glang.TermIdent("unsafe.Pointer")
	}
	return glang.TermIdent("go." + t.Name())
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
	return glang.NewCallExpr(glang.TermIdent("go.Signature"),
		argTypes,
		variadic,
		resultTypes,
	)
}

func (ctx *Ctx) interfaceType(n locatable, t *types.Interface) glang.Expr {
	var elems glang.ListExpr
	for i := range t.NumExplicitMethods() {
		elems = append(elems,
			glang.NewCallExpr(glang.TermIdent("go.MethodElem"),
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
					glang.TermIdent(typeTermCons),
					ctx.glangType(n, uem.Term(j).Type())),
				)
			}
		} else {
			terms = append(terms, glang.NewCallExpr(
				glang.TermIdent("go.TypeTerm"),
				ctx.glangType(n, em)),
			)
		}
		elems = append(elems,
			glang.NewCallExpr(glang.TermIdent("go.TypeElem"), terms))
	}

	return glang.NewCallExpr(glang.TermIdent("go.InterfaceType"), elems)
}

func (ctx *Ctx) glangType(n locatable, t types.Type) glang.Expr {
	switch t := t.(type) {
	case *types.Struct:
		// an anonymous struct type with fields: its synthetic declaration's type
		// (declared, like every named type's, before the code that uses it; its
		// TypeAssumptions relate it to its go.StructType)
		if name, ok := ctx.anonStructName(t); ok {
			return glang.TypeIdent(name)
		}
		return ctx.structType(t)
	case *types.TypeParam:
		return glang.TermIdent(t.Obj().Name())
	case *types.Basic:
		return ctx.basicType(t)
	case *types.Pointer:
		return glang.NewCallExpr(glang.VerbatimExpr("go.PointerType"), ctx.glangType(n, t.Elem()))
	case *types.Named:
		if t.Obj().Pkg() == nil {
			switch t.Obj().Name() {
			case "error", "any", "comparable":
				return glang.TermIdent("go." + t.Obj().Name())
			}
			ctx.nope(n, "unexpected built-in type %v", t.Obj())
		}
		if t.TypeArgs().Len() != 0 {
			return glang.CallExpr{
				MethodName: glang.TypeIdent(ctx.qualifiedName(t.Obj())),
				Args:       ctx.convertTypeArgsToGlang(n, t.TypeArgs()),
			}
		} else {
			return glang.TypeIdent(ctx.qualifiedName(t.Obj()))
		}
	case *types.Alias:
		if t.Obj().Pkg() == nil {
			switch t.Obj().Name() {
			case "error", "any", "comparable":
				return glang.TermIdent("go." + t.Obj().Name())
			}
			ctx.nope(n, "unexpected built-in type %v", t.Obj())
		}
		if t.TypeArgs().Len() != 0 {
			return glang.CallExpr{
				MethodName: glang.TypeIdent(ctx.qualifiedName(t.Obj())),
				Args:       ctx.convertTypeArgsToGlang(n, t.TypeArgs()),
			}
		} else {
			return glang.TypeIdent(ctx.qualifiedName(t.Obj()))
		}

	case *types.Map:
		return glang.NewCallExpr(glang.TermIdent("go.MapType"),
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
		return glang.NewCallExpr(glang.TermIdent("go.ChannelType"),
			glang.TermIdent(chanDir), ctx.glangType(n, t.Elem()),
		)
	case *types.Array:
		return glang.NewCallExpr(glang.VerbatimExpr("go.ArrayType"),
			glang.ZLiteral{Value: big.NewInt(t.Len())}, ctx.glangType(n, t.Elem()))
	case *types.Signature:
		return glang.NewCallExpr(glang.TermIdent("go.FunctionType"), ctx.signature(n, t))
	case *types.Interface:
		return ctx.interfaceType(n, t)
	case *types.Slice:
		return glang.NewCallExpr(glang.TermIdent("go.SliceType"), ctx.glangType(n, t.Elem()))
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
	// an anonymous struct type (name is its synthetic declaration's)
	anon bool
}

func (ctx *Ctx) structInfoToGlangType(info structTypeInfo) glang.Expr {
	return glang.TypeIdent(info.name)
}

// structInfoGoType is the Go type of the struct (for StructFieldRef).
func (ctx *Ctx) structInfoGoType(n locatable, info structTypeInfo) glang.Expr {
	if info.anon {
		return glang.TypeIdent(info.name)
	}
	return ctx.glangType(n, info.namedType)
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
	if st, ok := t.(*types.Struct); ok {
		if name, ok := ctx.anonStructName(st); ok {
			return structTypeInfo{
				name:           name,
				throughPointer: throughPointer,
				structType:     st,
				anon:           true,
			}, true
		}
	}
	return structTypeInfo{}, false
}

// basicLeanType is the Lean type modeling the values of a basic Go type
func (ctx *Ctx) basicLeanType(n locatable, t *types.Basic) string {
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
		return "Bool"
	case "string", "untyped string":
		return "GoString"
	case "uintptr":
		// the semantics models uintptr as a 64-bit unsigned integer
		return "w64"
	case "Pointer":
		return "Loc"
	}
	ctx.unsupported(n, "Unknown basic type %s,", t.Name())
	return ""
}
