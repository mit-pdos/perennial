package goose

import (
	"go/ast"
	"go/types"

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
