package proofgen

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"iter"
	"log"
	"slices"
	"strconv"
	"strings"

	"github.com/mit-pdos/perennial/goose"
	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/mit-pdos/perennial/goose/proofgen/tmpl"
	"github.com/mit-pdos/perennial/goose/util"
	"github.com/mit-pdos/perennial/goose/util/toposort"
	"golang.org/x/tools/go/packages"
)

type typesTranslator struct {
	pkg *packages.Package

	specs          []*ast.TypeSpec
	nameToTypeSpec map[string]*ast.TypeSpec

	filter declfilter.DeclFilter
}

func (tr typesTranslator) ReadablePos(p token.Pos) string {
	return tr.pkg.Fset.Position(p).String()
}

func (tr *typesTranslator) translateStructType(spec *ast.TypeSpec, s *types.Struct) []tmpl.TypeDecl {
	decl := tr.newTypeDecl(spec, false)
	if spec.TypeParams != nil {
		for _, tp := range spec.TypeParams.List {
			for _, name := range tp.Names {
				decl.TypeParams = append(decl.TypeParams, name.Name)
			}
		}
	}
	decl.LeanFields = tr.leanFields(s)
	return []tmpl.TypeDecl{decl}
}

func (tr *typesTranslator) leanFields(s *types.Struct) []tmpl.LeanField {
	var fields []tmpl.LeanField
	for i := 0; i < s.NumFields(); i++ {
		fieldName := s.Field(i).Name()
		if fieldName == "_" {
			fieldName = "_#" + strconv.Itoa(i)
		}
		fields = append(fields, tmpl.LeanField{
			Name:     fieldName,
			Proj:     glang.LeanQuoteComponent(fieldName + "'"),
			GoString: glang.LeanStringLit(fieldName),
			// iNamed needs the name to parse as an identifier
			HypName: leanHypName(fieldName),
			Type:    tr.toLeanType(s.Field(i).Type()),
		})
	}
	return fields
}

// anonStructDecl is the TypeDecl of an unnamed struct type of the translation
// (goose.AnonStructs), modeled like a defined struct type.
func (tr *typesTranslator) anonStructDecl(a goose.AnonStruct) tmpl.TypeDecl {
	decl := tmpl.TypeDecl{
		PkgName:    glang.LeanNamespace(tr.pkg.PkgPath),
		Name:       glang.LeanQuoteComponent(a.Name),
		RawName:    a.Name,
		ImplName:   glang.LeanIdent(glang.TypeImpl(a.Name)),
		TypeParams: a.TypeParams,
		Axiomatize: a.Axiomatized,
	}
	if !a.Axiomatized {
		decl.LeanFields = tr.leanFields(a.Struct)
	}
	return decl
}

func (tr *typesTranslator) translateType(spec *ast.TypeSpec) []tmpl.TypeDecl {
	if tr.filter.GetAction(spec.Name.Name) == declfilter.Axiomatize {
		decl := tr.newTypeDecl(spec, true)
		if spec.TypeParams != nil {
			for _, tp := range spec.TypeParams.List {
				for _, name := range tp.Names {
					decl.TypeParams = append(decl.TypeParams, name.Name)
				}
			}
		}
		return []tmpl.TypeDecl{decl}
	}

	switch s := tr.pkg.TypesInfo.TypeOf(spec.Type).(type) {
	case *types.Struct:
		return tr.translateStructType(spec, s)
	}
	return nil
}

func (tr *typesTranslator) Decl(d ast.Decl) {
	switch d := d.(type) {
	case *ast.FuncDecl:
		// the types declared in a translated function (see util.TypeDecls)
		fn, ok := tr.pkg.TypesInfo.Defs[d.Name].(*types.Func)
		if ok && tr.filter.GetAction(util.FuncName(fn)) == declfilter.Translate {
			for _, g := range util.TypeDecls(d) {
				tr.Decl(g)
			}
		}
	case *ast.GenDecl:
		switch d.Tok {
		case token.TYPE:
			for _, spec := range d.Specs {
				spec := spec.(*ast.TypeSpec)
				if spec.Assign == token.NoPos {
					switch tr.filter.GetAction(spec.Name.Name) {
					case declfilter.Translate, declfilter.Axiomatize:
						tr.specs = append(tr.specs, spec)
						tr.nameToTypeSpec[spec.Name.Name] = spec
						continue
					case declfilter.Trust:
						continue
					}
				}
			}
		}
	case *ast.BadDecl:
	default:
	}
}

// translatedType is a type declaration with the (same-package) type
// declarations its generated proofs depend on.
type translatedType struct {
	decl tmpl.TypeDecl
	name string
	deps []string
}

func translateTypes(pkg *packages.Package, filter declfilter.DeclFilter) []tmpl.TypeDecl {
	var decls []tmpl.TypeDecl
	for _, t := range translateTypesDeps(pkg, filter) {
		decls = append(decls, t.decl)
	}
	return decls
}

func translateTypesDeps(pkg *packages.Package, filter declfilter.DeclFilter) []translatedType {
	tr := &typesTranslator{
		pkg:            pkg,
		filter:         filter,
		nameToTypeSpec: make(map[string]*ast.TypeSpec),
	}
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			tr.Decl(d)
		}
	}

	var decls []translatedType

	// the unnamed struct types, each emitted before the first type whose
	// values contain it (and after those its own values contain)
	anonByName := make(map[string]goose.AnonStruct)
	anons := goose.AnonStructs(pkg, filter)
	for _, a := range anons {
		anonByName[a.Name] = a
	}
	anonDeps := func(def types.Type) []string {
		var deps []string
		for _, s := range util.AnonStructsInDef(def) {
			if _, ok := anonByName[util.AnonStructName(s)]; ok {
				deps = append(deps, util.AnonStructName(s))
			}
		}
		return deps
	}
	emitted := make(map[string]bool)
	var emitAnon func(name string)
	emitAnon = func(name string) {
		a, ok := anonByName[name]
		if !ok || emitted[name] {
			return
		}
		emitted[name] = true
		for _, dep := range anonDeps(a.Struct) {
			emitAnon(dep)
		}
		var deps []string
		for n := range util.TypeGetDependencies(pkg.PkgPath, a.Struct) {
			if _, ok := tr.nameToTypeSpec[n]; ok {
				deps = append(deps, n)
			}
		}
		decls = append(decls, translatedType{decl: tr.anonStructDecl(a), name: name,
			deps: append(deps, anonDeps(a.Struct)...)})
	}

	depsOf := func(s *ast.TypeSpec) []string {
		var deps []string
		if tr.filter.GetAction(s.Name.Name) == declfilter.Axiomatize {
			return nil
		}
		for n := range util.TypeGetDependencies(pkg.PkgPath, pkg.TypesInfo.TypeOf(s.Type)) {
			if _, ok := tr.nameToTypeSpec[n]; ok && n != s.Name.Name {
				deps = append(deps, n)
			}
		}
		return append(deps, anonDeps(pkg.TypesInfo.TypeOf(s.Type))...)
	}

	for t := range toposort.ToposortSeq(slices.Values(tr.specs),
		func(s *ast.TypeSpec) iter.Seq[*ast.TypeSpec] {
			return func(yield func(s *ast.TypeSpec) bool) {
				if tr.filter.GetAction(s.Name.Name) == declfilter.Axiomatize {
					return
				}
				for n := range util.TypeGetDependencies(pkg.PkgPath, pkg.TypesInfo.TypeOf(s.Type)) {
					if t, ok := tr.nameToTypeSpec[n]; ok {
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
			log.Fatal(cycle[0], "%s", s)
		}) {
		if tr.filter.GetAction(t.Name.Name) != declfilter.Axiomatize {
			for _, dep := range anonDeps(pkg.TypesInfo.TypeOf(t.Type)) {
				emitAnon(dep)
			}
		}
		for _, d := range tr.translateType(t) {
			decls = append(decls, translatedType{decl: d, name: t.Name.Name, deps: depsOf(t)})
		}
	}
	for _, a := range anons {
		emitAnon(a.Name)
	}
	return decls
}

func (tr *typesTranslator) newTypeDecl(spec *ast.TypeSpec, axiomatize bool) tmpl.TypeDecl {
	rawName := glang.ToIdent(spec.Name.Name)
	return tmpl.TypeDecl{
		PkgName:    glang.LeanNamespace(tr.pkg.PkgPath),
		Name:       glang.LeanIdent(spec.Name.Name),
		RawName:    rawName,
		ImplName:   glang.LeanIdent(glang.TypeImpl(rawName)),
		TypeParams: nil, // populated by caller
		Axiomatize: axiomatize,
	}
}

// toLeanType is the Lean type modeling a Go type (cf. goose's toLeanType)
func (tr *typesTranslator) toLeanType(t types.Type) string {
	switch t := types.Unalias(t).(type) {
	case *types.Basic:
		switch t.Name() {
		case "uint64", "int64", "uint", "int", "float64", "uintptr":
			return "w64"
		case "uint32", "int32", "float32":
			return "w32"
		case "uint16", "int16":
			return "w16"
		case "uint8", "int8", "byte":
			return "w8"
		case "bool":
			return "Bool"
		case "string", "untyped string":
			return "GoString"
		case "Pointer":
			return "Loc"
		}
		log.Fatalf("unknown basic type %s", t.Name())
	case *types.Slice:
		return "GoSlice"
	case *types.Array:
		return fmt.Sprintf("(GoArray %s %d)", tr.toLeanType(t.Elem()), t.Len())
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
		var base string
		if pkg := t.Obj().Pkg(); pkg != nil {
			base = glang.LeanNamespace(pkg.Path()) + "." + glang.LeanQuote(glang.ToIdent(t.Obj().Name()))
		} else {
			// universe types (error) are modeled by the framework
			base = glang.LeanUniverseType(t.Obj().Name())
		}
		if t.TypeArgs().Len() > 0 {
			var params []string
			for i := 0; i < t.TypeArgs().Len(); i++ {
				params = append(params, tr.toLeanType(t.TypeArgs().At(i)))
			}
			return fmt.Sprintf("(%s %s)", base, strings.Join(params, " "))
		}
		return base
	case *types.TypeParam:
		return glang.LeanQuote(t.Obj().Name() + "'")
	case *types.Struct:
		if t.NumFields() == 0 {
			return "Unit"
		}
		base := glang.LeanNamespace(tr.pkg.PkgPath) + "." + glang.LeanQuoteComponent(util.AnonStructName(t))
		var params []string
		for _, p := range util.AnonStructParams(t) {
			params = append(params, tr.toLeanType(p))
		}
		if len(params) == 0 {
			return base
		}
		return fmt.Sprintf("(%s %s)", base, strings.Join(params, " "))
	}
	log.Fatalf("unsupported type %s in struct field", t)
	return ""
}

func leanHypName(s string) string {
	if glang.LeanQuoteComponent(s) != s {
		if glang.LeanQuoteComponent(s+"'") == s+"'" {
			s = s + "'"
		} else {
			s = glang.LeanQuoteComponent(s)
		}
	}
	return glang.LeanRawString(s)
}
