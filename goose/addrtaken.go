package goose

import (
	"go/ast"
	"go/token"
	"go/types"
)

// rootVar returns the variable whose storage the addressable expression e is
// part of (through fields and array elements, not through pointers), or nil. An
// index of a type parameter may be an array's or a slice's: conservative counts it as
// in the variable (to mark address-taken variables), otherwise it does not (to find
// unaliased ones).
func rootVar(info *types.Info, e ast.Expr, conservative bool) *types.Var {
	switch e := ast.Unparen(e).(type) {
	case *ast.Ident:
		v, _ := info.Uses[e].(*types.Var)
		return v
	case *ast.SelectorExpr:
		if sel := info.Selections[e]; sel != nil && sel.Kind() == types.FieldVal && !sel.Indirect() {
			return rootVar(info, e.X, conservative)
		}
	case *ast.IndexExpr:
		t := info.TypeOf(e.X)
		if _, isTP := t.(*types.TypeParam); isTP && conservative || !isTP && inPlace(t) {
			return rootVar(info, e.X, conservative)
		}
	}
	return nil
}

// inPlace reports whether indexing or slicing an operand of type t reaches into the
// operand's own storage: an array, or a type parameter (whose core type may be one), not a
// slice, string, map or pointer.
func inPlace(t types.Type) bool {
	if _, isTP := t.(*types.TypeParam); isTP {
		return true
	}
	_, ok := t.Underlying().(*types.Array)
	return ok
}

// addrTakenVars returns the variables of the package whose address is taken:
// `&x`, slicing an array variable, or calling a pointer method on it. No
// pointer into the storage of any other variable exists.
func addrTakenVars(info *types.Info, files []*ast.File) map[*types.Var]bool {
	m := make(map[*types.Var]bool)
	mark := func(e ast.Expr) {
		if v := rootVar(info, e, true); v != nil {
			m[v] = true
		}
	}
	for _, f := range files {
		ast.Inspect(f, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.UnaryExpr:
				if n.Op == token.AND {
					mark(n.X)
				}
			case *ast.SliceExpr:
				if inPlace(info.TypeOf(n.X)) {
					mark(n.X)
				}
			case *ast.SelectorExpr:
				if sel := info.Selections[n]; sel != nil && sel.Kind() == types.MethodVal {
					sig := sel.Obj().Type().(*types.Signature)
					_, ptrRecv := sig.Recv().Type().Underlying().(*types.Pointer)
					_, ptrX := info.TypeOf(n.X).Underlying().(*types.Pointer)
					if ptrRecv && !ptrX {
						mark(n.X)
					}
				}
			}
			return true
		})
	}
	return m
}
