package goose

// Skipped package variables (the `skip` entries of a package's goose config,
// declfilter.SkipEntry).
//
// A skipped variable is not translated at all: goose emits no Lean name for
// it, no X.init, no GlobalAlloc and no step in initialize'. What remains
// trusted is each entry's reason: that not running the variable's Go
// initializer is unobservable. The design points (D1-D11 of the plan on
// etcd-grove#19) are marked where they are decided, so that each can be
// revised on its own.

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"strings"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"golang.org/x/tools/go/packages"
)

// configError is an error in a package's goose config (not at a position in
// the Go source).
func configError(pkgPath string, err error) *ConversionError {
	return &ConversionError{
		Category:    "unsupported",
		Message:     fmt.Sprintf("goose config of %s: %v", pkgPath, err),
		GooseCaller: getCaller(1),
	}
}

// checkSkipConfig returns the errors of the package's skip entries: those the
// config alone shows (declfilter.FilterConfig.CheckSkip) and those that need
// the package: a name that is not one of its package-level variables (a stale
// entry, e.g. after a Go upgrade; "_" needs at least one blank variable), and
// an initializer of several variables that is only partly skipped (D5: the
// initializer, one Go evaluation, is the unit).
func (ctx *Ctx) checkSkipConfig(pkg *packages.Package, config declfilter.FilterConfig) (errs []error) {
	for _, err := range config.CheckSkip() {
		errs = append(errs, configError(pkg.PkgPath, err))
	}
	if len(errs) > 0 {
		return
	}
	hasBlank := false
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			if d, ok := d.(*ast.GenDecl); ok && d.Tok == token.VAR {
				for _, s := range d.Specs {
					for _, n := range s.(*ast.ValueSpec).Names {
						hasBlank = hasBlank || n.Name == "_"
					}
				}
			}
		}
	}
	for _, e := range config.Skip {
		for _, n := range e.Names {
			if n == "_" {
				if !hasBlank {
					errs = append(errs, configError(pkg.PkgPath,
						fmt.Errorf(`skip name "_": the package has no blank package variable`)))
				}
				continue
			}
			if _, ok := pkg.Types.Scope().Lookup(n).(*types.Var); !ok {
				errs = append(errs, configError(pkg.PkgPath,
					fmt.Errorf("skip name %q is not a package-level variable of the package", n)))
			}
		}
	}
	var e errorCatcher
	for _, init := range ctx.info.InitOrder {
		var skipped, kept []string
		for _, v := range init.Lhs {
			if ctx.filter.GetAction(v.Name()) == declfilter.Skip {
				skipped = append(skipped, v.Name())
			} else {
				kept = append(kept, v.Name())
			}
		}
		if len(skipped) > 0 && len(kept) > 0 {
			e.do(func() {
				ctx.unsupported(init.Lhs[0],
					"the initializer of %s is only partly skipped (skipped: %s; not skipped: %s): "+
						"skip all of its variables or none",
					varNames(init.Lhs), strings.Join(skipped, ", "), strings.Join(kept, ", "))
			})
		}
	}
	for _, err := range e.errs {
		errs = append(errs, err)
	}
	return
}

func varNames(vs []*types.Var) string {
	var ns []string
	for _, v := range vs {
		ns = append(ns, v.Name())
	}
	return strings.Join(ns, ", ")
}
