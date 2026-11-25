package goose

import (
	"go/ast"
	"go/types"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/util"
)

// checkModelLayouts refuses every call of unsafe.Sizeof, unsafe.Alignof and
// unsafe.Offsetof in the files whose operand's type contains a type whose
// layout a Go model changes (util.Models.LayoutChanged; for Offsetof, the
// type of the struct the selector selects from): Go folds such a call to a
// constant from gc's layout of the real type, which the model's type does
// not have.
func (ctx *Ctx) checkModelLayouts(files []*ast.File, models *util.Models) []error {
	var e errorCatcher
	for _, f := range files {
		ast.Inspect(f, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok || len(call.Args) != 1 {
				return true
			}
			var id *ast.Ident
			switch fun := ast.Unparen(call.Fun).(type) {
			case *ast.Ident:
				id = fun
			case *ast.SelectorExpr:
				id = fun.Sel
			}
			b, ok := ctx.info.Uses[id].(*types.Builtin)
			if id == nil || !ok {
				return true
			}
			var t types.Type
			switch b.Name() {
			case "Sizeof", "Alignof":
				t = ctx.info.TypeOf(call.Args[0])
			case "Offsetof":
				if sel, ok := ast.Unparen(call.Args[0]).(*ast.SelectorExpr); ok {
					t = ctx.info.TypeOf(sel.X)
				}
			}
			if t == nil {
				return true
			}
			if name, changed := models.LayoutChanged(t); changed {
				e.do(func() {
					ctx.unsupported(call, "unsafe.%s of a type containing %s, whose layout its Go model "+
						"changes (Go's value is gc's layout of the real type)", b.Name(), name)
				})
			}
			return true
		})
	}
	return e.errs
}

// checkModelDecls refuses every type declaration `type M N` in the files
// (not an alias; local ones included) whose type N is a named type whose
// layout a Go model changes (util.Models.LayoutModelled), or is declared so
// itself in these files, transitively. Go gives M the underlying type of the
// real N, the translation that of N's model; and go.layoutModelled, which
// makes such a type opaque to reflection, lists only the names of the
// models' own types (generated once, for Perennial's packages), not M. (A
// declaration of another package over such a type is refused when that
// package is translated.) A declaration the config skips is not translated,
// and one listed itself (a trusted type) is opaque already.
func (ctx *Ctx) checkModelDecls(files []*ast.File, models *util.Models) []error {
	var specs []*ast.TypeSpec
	rhs := make(map[*types.TypeName]*types.TypeName)
	for _, f := range files {
		ast.Inspect(f, func(n ast.Node) bool {
			spec, ok := n.(*ast.TypeSpec)
			if !ok || spec.Assign.IsValid() {
				return true
			}
			obj, ok := ctx.info.Defs[spec.Name].(*types.TypeName)
			if !ok {
				return true
			}
			if named, ok := types.Unalias(ctx.info.TypeOf(spec.Type)).(*types.Named); ok {
				rhs[obj] = named.Origin().Obj()
				specs = append(specs, spec)
			}
			return true
		})
	}
	// over returns the type whose layout a model changes that o is declared
	// over, directly or through declarations of these files.
	over := func(o *types.TypeName) (string, bool) {
		seen := make(map[*types.TypeName]bool)
		for o != nil && !seen[o] {
			seen[o] = true
			if name, ok := models.LayoutModelled(o); ok {
				return name, true
			}
			o = rhs[o]
		}
		return "", false
	}
	var e errorCatcher
	for _, spec := range specs {
		obj := ctx.info.Defs[spec.Name].(*types.TypeName)
		if _, listed := models.LayoutModelled(obj); listed {
			continue
		}
		if obj.Parent() == obj.Pkg().Scope() && ctx.filter.GetAction(obj.Name()) == declfilter.Skip {
			continue
		}
		if name, ok := over(rhs[obj]); ok {
			e.do(func() {
				ctx.unsupported(spec, "type %s declared over %s, whose layout its Go model changes "+
					"(Go's underlying type is the real type's)", obj.Name(), name)
			})
		}
	}
	return e.errs
}
