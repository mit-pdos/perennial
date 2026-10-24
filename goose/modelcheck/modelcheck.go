// Package modelcheck finds Go code that goose's semantics is known to model
// incorrectly, so that goose can refuse to translate it.
//
// It checks one construct (docs/design/unsafe-memory.md, R4, and section 5, L1
// overlapping whole copies): the copy of a value between two
// memory places,
//
//	lhs = rhs
//
// where lhs and rhs are both memory places (a dereference, a field or an
// element of an addressable value, or a conversion of one of these, but not a
// whole variable), of a type that is, or could be for some instantiation, a
// plain struct or array type. The semantics copies the value with a whole
// load followed by a whole store, which behaves like memmove. gc compiles the
// statement to a Move, which assumes that its source and destination do not
// partially overlap, and copies forward in chunks; on views that do overlap,
// which unsafe can make, gc's result differs.
//
// The check is syntactic and conservative: it reports every such statement,
// including those whose sides can never overlap.
package modelcheck

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"sort"
)

// Finding is one statement the semantics may model incorrectly.
type Finding struct {
	Pos token.Position
	Msg string
}

func (f Finding) String() string {
	return fmt.Sprintf("%v: %s", f.Pos, f.Msg)
}

// sizes is the layout the semantics' plain types follow (gc on linux/amd64).
var sizes = types.SizesFor("gc", "amd64")

type checker struct {
	fset     *token.FileSet
	info     *types.Info
	findings []Finding
}

// CheckNodes reports the findings in the given syntax trees (function
// declarations, expressions, or whole files), sorted by position.
func CheckNodes(fset *token.FileSet, info *types.Info, nodes ...ast.Node) []Finding {
	c := &checker{fset: fset, info: info}
	for _, n := range nodes {
		ast.Inspect(n, c.visit)
	}
	sort.SliceStable(c.findings, func(i, j int) bool {
		a, b := c.findings[i].Pos, c.findings[j].Pos
		if a.Filename != b.Filename {
			return a.Filename < b.Filename
		}
		return a.Offset < b.Offset
	})
	return c.findings
}

func (c *checker) visit(n ast.Node) bool {
	switch s := n.(type) {
	case *ast.AssignStmt:
		// A multiple assignment is checked pair by pair: gc copies an operand
		// that no earlier assignment of the statement can affect directly,
		// without a temporary.
		if s.Tok == token.ASSIGN && len(s.Lhs) == len(s.Rhs) {
			for i := range s.Lhs {
				c.copyStmt(s, s.Lhs[i], s.Rhs[i])
			}
		}
	case *ast.RangeStmt:
		// for _, lhs = range x copies each element of x into lhs.
		if s.Tok == token.ASSIGN && s.Value != nil && c.isPlace(s.Value) {
			t := c.info.TypeOf(s.Value)
			if t != nil && mayBePlainComposite(t) && rangesOverMemory(c.info.TypeOf(s.X)) {
				c.report(s.Value, "range assignment of %s into a memory place (%s)",
					t, types.ExprString(s.Value))
			}
		}
	}
	return true
}

func (c *checker) copyStmt(s *ast.AssignStmt, lhs, rhs ast.Expr) {
	t := c.info.TypeOf(lhs)
	if t == nil || !mayBePlainComposite(t) {
		return
	}
	if !c.isPlace(lhs) || !c.isSource(rhs) || c.sameRoot(lhs, rhs) {
		return
	}
	c.report(s, "copy of %s between two memory places (%s = %s)",
		t, types.ExprString(lhs), types.ExprString(rhs))
}

func (c *checker) report(n ast.Node, format string, args ...any) {
	c.findings = append(c.findings, Finding{
		Pos: c.fset.Position(n.Pos()),
		Msg: fmt.Sprintf(format, args...) +
			": the semantics copies by value, but gc does not if the two sides partially overlap" +
			" (docs/design/unsafe-memory.md, R4)",
	})
}

// under is t's underlying type, or nil for a type parameter. The checks below
// treat a type parameter as any type it could be, which only adds findings.
func under(t types.Type) types.Type {
	if t == nil {
		return nil
	}
	if _, ok := types.Unalias(t).(*types.TypeParam); ok {
		return nil
	}
	return t.Underlying()
}

// rangesOverMemory reports whether a range over a value of type t may read its
// elements from memory (an array, a pointer to one, or a slice).
func rangesOverMemory(t types.Type) bool {
	switch u := under(t).(type) {
	case nil, *types.Array, *types.Slice:
		return true
	case *types.Pointer:
		switch under(u.Elem()).(type) {
		case nil, *types.Array:
			return true
		}
	}
	return false
}

// isSource reports whether rhs, the right side of a copy, is read directly
// from a memory place: a place, or a conversion of a slice to an array.
func (c *checker) isSource(rhs ast.Expr) bool {
	if conv, ok := c.conversion(rhs); ok {
		from, to := under(c.info.TypeOf(conv.Args[0])), under(c.info.TypeOf(conv))
		_, fromSlice := from.(*types.Slice)
		_, toArray := to.(*types.Array)
		if (fromSlice || from == nil) && (toArray || to == nil) {
			return true // [N]T(s) reads from s's array
		}
	}
	return c.isPlace(rhs)
}

// isPlace reports whether e denotes a memory place other than a whole
// variable: a dereference, a field or element of an addressable value, or a
// value-preserving conversion of a place. A whole variable is its own block of
// exactly its type's size, so no other view of that type can partially overlap
// it without leaving the block, which the semantics makes stuck (design R3).
func (c *checker) isPlace(e ast.Expr) bool {
	e = ast.Unparen(e)
	switch e := e.(type) {
	case *ast.StarExpr:
		return true
	case *ast.SelectorExpr:
		sel := c.info.Selections[e]
		if sel == nil || sel.Kind() != types.FieldVal {
			return false // a qualified identifier (pkg.V) is a whole variable
		}
		if sel.Indirect() {
			return true // through a pointer, possibly an embedded one
		}
		return c.addressable(e.X)
	case *ast.IndexExpr:
		if tv, ok := c.info.Types[e.X]; !ok || !tv.IsValue() {
			return false // a generic instantiation
		}
		switch under(c.info.TypeOf(e.X)).(type) {
		case nil, *types.Slice, *types.Pointer:
			return true // a slice element or an element of *[N]T
		case *types.Array:
			return c.addressable(e.X)
		}
		return false // a map index or a string
	case *ast.CallExpr:
		if conv, ok := c.conversion(e); ok {
			from, to := under(c.info.TypeOf(conv.Args[0])), under(c.info.TypeOf(conv))
			if from == nil || to == nil || types.IdenticalIgnoreTags(from, to) {
				return c.isPlace(conv.Args[0]) // gc copies from the operand's memory
			}
		}
	}
	return false
}

// sameRoot reports whether lhs and rhs are places reached from one root by
// field selections, indexing and dereferences, with a root and indices that
// cannot change between the two evaluations (they contain no call other than a
// conversion or len/cap, and no receive). Such places cannot partially overlap:
// the layout of the root's value (the pointee of a dereferenced root, the
// backing array of an indexed slice) is a tree, so two places in it are
// disjoint or one contains the other, and two places of one size where one
// contains the other are the same place. A Move between disjoint places or
// onto the same place is a correct copy. For example data[i], data[j] =
// data[j], data[i] (sort's swap) and p.X = p.Y.
func (c *checker) sameRoot(lhs, rhs ast.Expr) bool {
	l, okL := c.root(lhs)
	r, okR := c.root(rhs)
	return okL && okR && types.ExprString(l) == types.ExprString(r)
}

// root peels the field selections, indexing, dereferences and
// value-preserving conversions off a place. It reports false if an index, or
// the root, could change the root's value during the statement.
func (c *checker) root(e ast.Expr) (ast.Expr, bool) {
	for {
		e = ast.Unparen(e)
		switch x := e.(type) {
		case *ast.StarExpr:
			e = x.X
			continue
		case *ast.SelectorExpr:
			if sel := c.info.Selections[x]; sel != nil && sel.Kind() == types.FieldVal {
				e = x.X
				continue
			}
		case *ast.IndexExpr:
			switch under(c.info.TypeOf(x.X)).(type) {
			case *types.Slice, *types.Pointer, *types.Array:
				if !c.callFree(x.Index) {
					return nil, false
				}
				e = x.X
				continue
			}
			// A type parameter may be a map, whose elements are not a tree.
			return nil, false
		case *ast.CallExpr:
			if conv, ok := c.conversion(x); ok {
				from, to := under(c.info.TypeOf(conv.Args[0])), under(c.info.TypeOf(conv))
				if from != nil && to != nil && types.IdenticalIgnoreTags(from, to) {
					e = conv.Args[0]
					continue
				}
			}
		}
		return e, c.callFree(e)
	}
}

// callFree reports whether evaluating e cannot change memory: it contains no
// call other than a conversion or len/cap, no function literal and no receive.
func (c *checker) callFree(e ast.Expr) bool {
	free := true
	ast.Inspect(e, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			free = false
		case *ast.UnaryExpr:
			if n.Op == token.ARROW {
				free = false
			}
		case *ast.CallExpr:
			if _, ok := c.conversion(n); ok {
				return true
			}
			if id, ok := ast.Unparen(n.Fun).(*ast.Ident); ok {
				if b, ok := c.info.Uses[id].(*types.Builtin); ok && (b.Name() == "len" || b.Name() == "cap") {
					return true
				}
			}
			free = false
		}
		return free
	})
	return free
}

// addressable reports whether e is addressable: a variable, or a place.
func (c *checker) addressable(e ast.Expr) bool {
	e = ast.Unparen(e)
	switch e := e.(type) {
	case *ast.Ident:
		_, isVar := c.info.Uses[e].(*types.Var)
		return isVar
	case *ast.SelectorExpr:
		if _, isVar := c.info.Uses[e.Sel].(*types.Var); isVar && c.info.Selections[e] == nil {
			return true // pkg.V
		}
	}
	return c.isPlace(e)
}

// conversion returns e as a type conversion, if it is one.
func (c *checker) conversion(e ast.Expr) (*ast.CallExpr, bool) {
	call, ok := ast.Unparen(e).(*ast.CallExpr)
	if !ok || len(call.Args) != 1 {
		return nil, false
	}
	tv, ok := c.info.Types[call.Fun]
	return call, ok && tv.IsType()
}

// mayBePlainComposite reports whether a value of type t is, or for some
// instantiation of its type parameters could be, of a plain struct or array
// type (design R1). Only those are copied with a Move that the semantics
// models incorrectly: a plain integer is one load and one store, and views of
// a non-plain type cannot partially overlap (design R3).
func mayBePlainComposite(t types.Type) bool {
	switch under(t).(type) {
	case nil, *types.Struct, *types.Array:
		return mayBePlain(t)
	}
	return false
}

// mayBePlain is the design's Plain (R1), where a type parameter may be
// instantiated to any plain type.
func mayBePlain(t types.Type) bool {
	switch u := under(t).(type) {
	case nil:
		return true
	case *types.Basic:
		switch u.Kind() {
		case types.Int, types.Int8, types.Int16, types.Int32, types.Int64,
			types.Uint, types.Uint8, types.Uint16, types.Uint32, types.Uint64, types.Uintptr:
			return true
		}
		return false
	case *types.Array:
		return u.Len() >= 1 && mayBePlain(u.Elem())
	case *types.Struct:
		if u.NumFields() == 0 {
			return false
		}
		generic := false
		for i := range u.NumFields() {
			f := u.Field(i)
			if f.Name() == "_" || !mayBePlain(f.Type()) {
				return false
			}
			generic = generic || hasTypeParam(f.Type())
		}
		// A struct whose layout depends on a type parameter may be unpadded
		// for some instantiation.
		return generic || unpadded(u)
	}
	return false
}

// unpadded reports whether a struct has no padding, trailing padding included.
func unpadded(s *types.Struct) bool {
	fields := make([]*types.Var, s.NumFields())
	for i := range fields {
		fields[i] = s.Field(i)
	}
	offsets := sizes.Offsetsof(fields)
	var end int64
	for i, f := range fields {
		if offsets[i] != end {
			return false
		}
		end += sizes.Sizeof(f.Type())
	}
	return end == sizes.Sizeof(s)
}

// hasTypeParam reports whether t's layout depends on a type parameter.
func hasTypeParam(t types.Type) bool {
	switch u := types.Unalias(t).(type) {
	case *types.TypeParam:
		return true
	case *types.Named:
		return hasTypeParam(u.Underlying())
	case *types.Array:
		return hasTypeParam(u.Elem())
	case *types.Struct:
		for i := range u.NumFields() {
			if hasTypeParam(u.Field(i).Type()) {
				return true
			}
		}
	}
	return false
}
