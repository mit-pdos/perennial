package order

import (
	"go/ast"
	"go/token"
	"go/types"
)

// lhsReads lists the operands that assigning to e reads: the index and
// pointer operands of the left side (spec, "Assignment statements"), not e's
// own value.
func (a *analysis) lhsReads(e ast.Expr) []ast.Expr {
	switch x := e.(type) {
	case *ast.ParenExpr:
		return a.lhsReads(x.X)
	case *ast.Ident:
		return nil
	case *ast.IndexExpr:
		if _, ok := a.under(x.X).(*types.Array); ok {
			return append(a.lhsReads(x.X), x.Index)
		}
		return []ast.Expr{x.X, x.Index}
	case *ast.StarExpr:
		return []ast.Expr{x.X}
	case *ast.SelectorExpr:
		if sel := a.info.Selections[x]; sel != nil && sel.Kind() == types.FieldVal {
			if _, ptr := a.under(x.X).(*types.Pointer); !ptr && !sel.Indirect() {
				return a.lhsReads(x.X)
			}
			if embeddedPointer(a.info.TypeOf(x.X), sel.Index()) {
				// a promoted field through an embedded pointer x.E: the
				// operands of the implicit indirections include x.E
				// (conservatively, the whole selector)
				return []ast.Expr{x}
			}
		}
		return []ast.Expr{x.X}
	}
	return []ast.Expr{e}
}

// embeddedPointer reports whether the field path idx from type t goes through
// an embedded field of pointer type (before its last step).
func embeddedPointer(t types.Type, idx []int) bool {
	for i, k := range idx {
		if p, ok := t.Underlying().(*types.Pointer); ok {
			t = p.Elem()
		}
		st, ok := t.Underlying().(*types.Struct)
		if !ok {
			return true // conservatively
		}
		t = st.Field(k).Type()
		if _, ptr := t.Underlying().(*types.Pointer); ptr && i < len(idx)-1 {
			return true
		}
	}
	return false
}

// assignUnit is the evaluation unit of an assignment: the operands its left
// side reads, then its right side.
func (a *analysis) assignUnit(s *ast.AssignStmt) []ast.Expr {
	var u []ast.Expr
	if s.Tok == token.DEFINE {
		// the left side is identifiers
	} else if s.Tok == token.ASSIGN {
		for _, l := range s.Lhs {
			u = append(u, a.lhsReads(l)...)
		}
	} else {
		u = append(u, s.Lhs...) // x op= y reads x
	}
	return append(u, s.Rhs...)
}

// callUnit is the evaluation unit of a go or defer statement: the function
// value and the arguments, evaluated now; the call itself runs later.
func callUnit(c *ast.CallExpr) []ast.Expr {
	return append([]ast.Expr{c.Fun}, c.Args...)
}

// selectUnit is the evaluation unit of a select statement: the channel and
// value operands of its cases, evaluated in source order on entry.
func selectUnit(s *ast.SelectStmt) []ast.Expr {
	var u []ast.Expr
	for _, c := range s.Body.List {
		cc := c.(*ast.CommClause)
		switch comm := cc.Comm.(type) {
		case *ast.SendStmt:
			u = append(u, comm.Chan, comm.Value)
		case *ast.ExprStmt:
			u = append(u, ast.Unparen(comm.X).(*ast.UnaryExpr).X)
		case *ast.AssignStmt:
			u = append(u, ast.Unparen(comm.Rhs[0]).(*ast.UnaryExpr).X)
		}
	}
	return u
}

// selectLhs lists the left-side operands of a select's receive cases,
// evaluated after the receive.
func (a *analysis) selectLhs(s *ast.SelectStmt) [][]ast.Expr {
	var u [][]ast.Expr
	for _, c := range s.Body.List {
		if as, ok := c.(*ast.CommClause).Comm.(*ast.AssignStmt); ok && as.Tok == token.ASSIGN {
			var r []ast.Expr
			for _, l := range as.Lhs {
				r = append(r, a.lhsReads(l)...)
			}
			u = append(u, r)
		}
	}
	return u
}

// headerNormal reports whether the parts of s that s itself evaluates (not
// the statements nested in it) are in normal form.
func (a *analysis) headerNormal(s ast.Stmt) bool {
	switch s := s.(type) {
	case nil:
		return true
	case *ast.ExprStmt:
		return a.unitNormal([]ast.Expr{s.X})
	case *ast.SendStmt:
		return a.unitNormal([]ast.Expr{s.Chan, s.Value})
	case *ast.IncDecStmt:
		return a.unitNormal([]ast.Expr{s.X})
	case *ast.AssignStmt:
		return a.unitNormal(a.assignUnit(s))
	case *ast.ReturnStmt:
		return a.unitNormal(s.Results)
	case *ast.GoStmt:
		return a.unitNormal(callUnit(s.Call))
	case *ast.DeferStmt:
		return a.unitNormal(callUnit(s.Call))
	case *ast.DeclStmt:
		if gd, ok := s.Decl.(*ast.GenDecl); ok && gd.Tok == token.VAR {
			for _, sp := range gd.Specs {
				if !a.unitNormal(sp.(*ast.ValueSpec).Values) {
					return false
				}
			}
		}
		return true
	case *ast.IfStmt:
		return a.headerNormal(s.Init) && a.unitNormal([]ast.Expr{s.Cond})
	case *ast.ForStmt:
		return a.headerNormal(s.Init) && a.headerNormal(s.Post) &&
			(s.Cond == nil || a.unitNormal([]ast.Expr{s.Cond}))
	case *ast.RangeStmt:
		if !a.unitNormal([]ast.Expr{s.X}) {
			return false
		}
		if s.Tok == token.ASSIGN {
			var r []ast.Expr
			for _, l := range []ast.Expr{s.Key, s.Value} {
				if l != nil {
					r = append(r, a.lhsReads(l)...)
				}
			}
			return a.unitNormal(r)
		}
		return true
	case *ast.SwitchStmt:
		if !a.headerNormal(s.Init) || (s.Tag != nil && !a.unitNormal([]ast.Expr{s.Tag})) {
			return false
		}
		return a.casesNormal(s)
	case *ast.TypeSwitchStmt:
		return a.headerNormal(s.Init) && a.unitNormal([]ast.Expr{typeSwitchX(s)})
	case *ast.SelectStmt:
		if !a.unitNormal(selectUnit(s)) {
			return false
		}
		for _, u := range a.selectLhs(s) {
			if !a.unitNormal(u) {
				return false
			}
		}
		return true
	case *ast.LabeledStmt:
		return a.headerNormal(s.Stmt)
	}
	return true
}

// casesNormal reports whether each case expression of s, compared with the
// switch's tag (evaluated once) in turn, is in normal form.
func (a *analysis) casesNormal(s *ast.SwitchStmt) bool {
	for _, c := range s.Body.List {
		for _, e := range c.(*ast.CaseClause).List {
			if !a.unitNormal([]ast.Expr{e}) {
				return false
			}
		}
	}
	return true
}

func typeSwitchX(s *ast.TypeSwitchStmt) ast.Expr {
	switch as := s.Assign.(type) {
	case *ast.AssignStmt:
		return ast.Unparen(as.Rhs[0]).(*ast.TypeAssertExpr).X
	case *ast.ExprStmt:
		return ast.Unparen(as.X).(*ast.TypeAssertExpr).X
	}
	return nil
}

// Violation is a statement (or package-level declaration) not in normal form.
type Violation struct {
	Pos  token.Pos
	Node ast.Node
}

// A Selection reports whether the declaration of the function or package-level
// variable obj is put in Perennial's order (goose translates it); nil
// selects every declaration.
type Selection func(obj types.Object) bool

// Selected reports whether sel selects the declaration d (a FuncDecl, or a
// package-level var spec one of whose variables it selects: goose translates
// each variable's initialization on its own).
func Selected(info *types.Info, sel Selection, d ast.Node) bool {
	if sel == nil {
		return true
	}
	switch d := d.(type) {
	case *ast.FuncDecl:
		return sel(info.Defs[d.Name])
	case *ast.ValueSpec:
		for _, n := range d.Names {
			if sel(info.Defs[n]) {
				return true
			}
		}
	}
	return false
}

// selectedDecls are the declarations of file that sel selects: function
// declarations and package-level var specs.
func selectedDecls(info *types.Info, file *ast.File, sel Selection) []ast.Node {
	var ds []ast.Node
	for _, d := range file.Decls {
		switch d := d.(type) {
		case *ast.FuncDecl:
			if d.Body != nil && Selected(info, sel, d) {
				ds = append(ds, d)
			}
		case *ast.GenDecl:
			if d.Tok == token.VAR {
				for _, sp := range d.Specs {
					if Selected(info, sel, sp) {
						ds = append(ds, sp)
					}
				}
			}
		}
	}
	return ds
}

// CheckFile lists the statements of the declarations of file that sel
// selects not in normal form, and the package-level variable declarations
// whose initializer is not.
func CheckFile(info *types.Info, file *ast.File, sel Selection) []Violation {
	a := newAnalysis(info, file)
	var vs []Violation
	for _, d := range selectedDecls(info, file, sel) {
		if vsp, ok := d.(*ast.ValueSpec); ok && !a.unitNormal(vsp.Values) {
			vs = append(vs, Violation{vsp.Pos(), vsp})
		}
		ast.Inspect(d, func(n ast.Node) bool {
			switch n.(type) {
			case *ast.BlockStmt, *ast.LabeledStmt, *ast.CaseClause, *ast.CommClause:
				return true
			}
			if s, ok := n.(ast.Stmt); ok && !a.headerNormal(s) {
				vs = append(vs, Violation{s.Pos(), s})
			}
			return true
		})
	}
	return vs
}
