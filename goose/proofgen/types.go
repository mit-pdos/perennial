package proofgen

import (
	"go/ast"
	"go/token"
	"go/types"
	"iter"
	"log"
	"slices"
	"strconv"

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
	decl := tmpl.TypeDecl{
		PkgName:    tr.pkg.Name,
		Name:       glang.GallinaIdent(spec.Name.Name).Coq(false),
		TypeParams: nil, // populated below
		Fields:     nil, // populated below
		Axiomatize: false,
	}
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
		decl.Fields = append(decl.Fields, fieldName)
	}
	return []tmpl.TypeDecl{decl}
}

func (tr *typesTranslator) translateType(spec *ast.TypeSpec) []tmpl.TypeDecl {
	if tr.filter.GetAction(spec.Name.Name) == declfilter.Axiomatize {
		decl := tmpl.TypeDecl{
			PkgName:    tr.pkg.Name,
			Name:       glang.GallinaIdent(spec.Name.Name).Coq(false),
			Axiomatize: true,
		}
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

func translateTypes(pkg *packages.Package, filter declfilter.DeclFilter) []tmpl.TypeDecl {
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

	var decls []tmpl.TypeDecl

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
		decls = append(decls, tr.translateType(t)...)
	}
	return decls
}
