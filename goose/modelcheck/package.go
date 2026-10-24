package modelcheck

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"

	"golang.org/x/tools/go/packages"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/util"
)

// CheckPackage reports the findings in the declarations of pkg that goose
// translates under the filter df: the bodies of translated functions and
// methods, and the initializers of translated package variables. Trusted and
// axiomatized declarations have no translated body, so they are not checked.
func CheckPackage(pkg *packages.Package, df declfilter.DeclFilter) []Finding {
	var nodes []ast.Node
	var inits []*ast.FuncDecl
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			if d, ok := d.(*ast.FuncDecl); ok && d.Recv == nil && d.Name.Name == "init" {
				inits = append(inits, d)
			}
		}
	}
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			switch d := d.(type) {
			case *ast.FuncDecl:
				if d.Body != nil && df.GetAction(declName(pkg.TypesInfo, inits, d)) == declfilter.Translate {
					nodes = append(nodes, d.Body)
				}
			case *ast.GenDecl:
				if d.Tok != token.VAR {
					continue
				}
				for _, spec := range d.Specs {
					spec := spec.(*ast.ValueSpec)
					if varsTranslated(df, spec) {
						for _, v := range spec.Values {
							nodes = append(nodes, v)
						}
					}
				}
			}
		}
	}
	return CheckNodes(pkg.Fset, pkg.TypesInfo, nodes...)
}

// declName is the name goose's filter knows a function declaration by (as in
// goose's funcDecl): T.M for a method, init.i for the i-th init function.
func declName(info *types.Info, inits []*ast.FuncDecl, d *ast.FuncDecl) string {
	if d.Recv != nil {
		return util.FuncName(info.ObjectOf(d.Name).(*types.Func))
	}
	if d.Name.Name == "init" {
		for i, init := range inits {
			if init == d {
				return fmt.Sprintf("init.%d", i)
			}
		}
	}
	return d.Name.Name
}

// varsTranslated reports whether goose translates a variable specification's
// initializer, which it does only when it translates every variable it sets.
func varsTranslated(df declfilter.DeclFilter, spec *ast.ValueSpec) bool {
	for _, name := range spec.Names {
		if df.GetAction(name.Name) != declfilter.Translate {
			return false
		}
	}
	return true
}
