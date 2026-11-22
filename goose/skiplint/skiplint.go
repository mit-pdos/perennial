// Package skiplint is a best-effort lint of the skip entries of goose
// configs (declfilter.SkipEntry; D9 of the design on etcd-grove#19). It is
// not part of the translator: goose neither runs it nor depends on its
// result, and what it finds is reported on the side (goose/cmd/skiplint,
// run by etc/update-goose-new.py).
//
// A skip entry's reason must show that not running the variable's Go
// initializer is unobservable: it terminates, cannot panic, and has no effect
// beyond the variable. Check points at one kind of effect beyond the
// variable that a reviewer could miss: a skipped initializer that stores to
// a package-level variable, or takes the address of one, directly or through
// the package's functions it calls (transitively).
//
// It is best-effort, not a check: every reason is still reviewed. It does
// not follow calls into other packages, method calls through interfaces or
// function values, or stores through a pointer it did not see taken (a
// pointer returned by a call, a method with a pointer receiver called on a
// package variable); it can warn about a store that is unobservable (to a
// variable the initializer itself allocates) or unreachable.
package skiplint

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"path/filepath"
	"strings"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"golang.org/x/tools/go/packages"
)

// skipped says whether the package variable v is skipped by the filter (a
// blank variable by its position, declfilter.BlankName).
func skipped(fset *token.FileSet, filter declfilter.DeclFilter, v *types.Var) bool {
	name := v.Name()
	if name == "_" {
		p := fset.Position(v.Pos())
		name = declfilter.BlankName(p.Filename, p.Line)
	}
	return filter.GetAction(name) == declfilter.Skip
}

// Check returns a warning for each skipped initializer of pkg (under filter)
// that stores to a package-level variable or takes the address of one,
// directly or through the package's functions it calls.
func Check(pkg *packages.Package, filter declfilter.DeclFilter) []string {
	info, fset := pkg.TypesInfo, pkg.Fset
	funcs := make(map[*types.Func]*ast.FuncDecl)
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			if d, ok := d.(*ast.FuncDecl); ok && d.Body != nil {
				if fn, ok := info.Defs[d.Name].(*types.Func); ok {
					funcs[fn] = d
				}
			}
		}
	}
	// the package variable whose memory e denotes (part of), if any
	pkgVar := func(e ast.Expr) (*types.Var, bool) {
		for {
			switch x := e.(type) {
			case *ast.ParenExpr:
				e = x.X
			case *ast.SelectorExpr:
				if v, ok := info.ObjectOf(x.Sel).(*types.Var); ok && !v.IsField() {
					return v, v.Parent() == v.Pkg().Scope()
				}
				e = x.X
			case *ast.IndexExpr:
				e = x.X
			case *ast.StarExpr:
				e = x.X
			case *ast.Ident:
				v, ok := info.ObjectOf(x).(*types.Var)
				return v, ok && v.Pkg() != nil && v.Parent() == v.Pkg().Scope()
			default:
				return nil, false
			}
		}
	}
	var warnings []string
	for _, init := range info.InitOrder {
		if !skipped(fset, filter, init.Lhs[0]) {
			continue
		}
		visited := make(map[*types.Func]bool)
		var effects []string
		var visit func(n ast.Node, where string)
		visit = func(n ast.Node, where string) {
			ast.Inspect(n, func(n ast.Node) bool {
				var lhs []ast.Expr
				what := "stores to"
				switch s := n.(type) {
				case *ast.AssignStmt:
					lhs = s.Lhs
				case *ast.IncDecStmt:
					lhs = []ast.Expr{s.X}
				case *ast.UnaryExpr:
					if s.Op == token.AND {
						lhs = []ast.Expr{s.X}
						what = "takes the address of"
					}
				case *ast.CallExpr:
					var id *ast.Ident
					switch f := s.Fun.(type) {
					case *ast.Ident:
						id = f
					case *ast.SelectorExpr:
						id = f.Sel
					}
					if id != nil {
						if fn, ok := info.Uses[id].(*types.Func); ok && !visited[fn] {
							if d, ok := funcs[fn]; ok {
								visited[fn] = true
								visit(d.Body, fn.Name())
							}
						}
					}
				}
				for _, l := range lhs {
					if v, ok := pkgVar(l); ok {
						pos := fset.Position(l.Pos())
						effects = append(effects, fmt.Sprintf("%s %s (in %s, %s:%d)",
							what, v.Name(), where, filepath.Base(pos.Filename), pos.Line))
					}
				}
				return true
			})
		}
		visit(init.Rhs, "the initializer")
		if len(effects) > 0 {
			var names []string
			for _, v := range init.Lhs {
				names = append(names, v.Name())
			}
			pos := fset.Position(init.Lhs[0].Pos())
			warnings = append(warnings, fmt.Sprintf(
				"%s:%d: skipped initializer of %s %s; "+
					"its skip reason must show this is unobservable",
				filepath.Base(pos.Filename), pos.Line, strings.Join(names, ", "),
				strings.Join(effects, ", ")))
		}
	}
	return warnings
}
