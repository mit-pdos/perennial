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
	for i := 0; i < s.NumFields(); i++ {
		fieldName := s.Field(i).Name()
		if fieldName == "_" {
			fieldName = "_" + strconv.Itoa(i)
		}
		decl.LeanFields = append(decl.LeanFields, tmpl.LeanField{
			Name:     fieldName,
			Proj:     glang.LeanQuoteComponent(fieldName + "'"),
			GoString: glang.LeanStringLit(fieldName),
			// iNamed needs the name to parse as an identifier
			HypName: leanHypName(fieldName),
			Type:    tr.toLeanType(s.Field(i).Type()),
		})
	}
	return []tmpl.TypeDecl{decl}
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
		// the types declared in the function (see util.TypeDecls)
		for _, g := range util.TypeDecls(d) {
			tr.Decl(g)
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
		return deps
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
		for _, d := range tr.translateType(t) {
			decls = append(decls, translatedType{decl: d, name: t.Name.Name, deps: depsOf(t)})
		}
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
	}
	log.Fatalf("unsupported type %s in struct field", t)
	return ""
}

func leanHypName(s string) string {
	if glang.LeanQuoteComponent(s) != s {
		s = s + "'"
	}
	return glang.LeanRawString(s)
}
