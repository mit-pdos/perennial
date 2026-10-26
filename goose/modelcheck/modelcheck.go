// Package modelcheck finds Go code that goose's semantics is known to model
// incorrectly, so that goose can refuse to translate it
// (docs/design/unsafe-memory.md, R4 and section 5).
//
// It checks one construct: the copy of a whole struct or array between two
// memory places,
//
//	lhs = rhs
//
// The semantics copies with a whole load followed by a whole store, which
// behaves like memmove. gc compiles the statement to a Move, which assumes
// that its source and destination do not partially overlap and copies forward
// in chunks; on views that do overlap, which unsafe can make, gc's result
// differs. The check is syntactic and conservative: it reports every such
// statement except those whose sides cannot partially overlap for one of two
// syntactic reasons (one side is a whole variable, or both sides have the
// same base).
//
// goose calls Assign and Range on each statement it translates, and
// PackageVar on each package-variable initializer, and reports a finding as an
// unsupported construct.
package modelcheck

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
)

// Prefix starts the message of every finding.
const Prefix = "modelcheck: "

type checker struct {
	info *types.Info
}

// Assign checks an assignment statement. It returns the first finding, as the
// node to report it at and a message, or ok = false if there is none.
func Assign(info *types.Info, s *ast.AssignStmt) (n ast.Node, msg string, ok bool) {
	if s.Tok != token.ASSIGN || len(s.Lhs) != len(s.Rhs) {
		return nil, "", false
	}
	c := checker{info}
	// A multiple assignment is checked pair by pair: gc may copy an operand
	// that no earlier assignment of the statement affects directly, without
	// a temporary.
	for i := range s.Lhs {
		lhs, rhs := s.Lhs[i], s.Rhs[i]
		t := info.TypeOf(lhs)
		if t == nil || !mayBeMoved(t) {
			continue
		}
		if !c.isPlace(lhs) || !c.isSource(rhs) || c.sameBase(lhs, rhs) {
			continue
		}
		return s, report("copy of %s between two memory places (%s = %s)",
			t, types.ExprString(lhs), types.ExprString(rhs)), true
	}
	return nil, "", false
}

// Range checks a range statement: for _, lhs = range x copies each element of
// x into lhs.
func Range(info *types.Info, s *ast.RangeStmt) (n ast.Node, msg string, ok bool) {
	if s.Tok != token.ASSIGN || s.Value == nil {
		return nil, "", false
	}
	c := checker{info}
	t := info.TypeOf(s.Value)
	if t == nil || !mayBeMoved(t) || !c.isPlace(s.Value) || !rangesOverMemory(info.TypeOf(s.X)) {
		return nil, "", false
	}
	return s.Value, report("range assignment of %s into a memory place (%s)",
		t, types.ExprString(s.Value)), true
}

// PackageVar checks the initializer of a package variable. gc builds a
// composite literal assigned to a package variable in place: each element is
// stored straight into its part of the variable, X.path = elem, through nested
// struct, array and slice literals (staticinit). Each such element is checked
// as that assignment; its left side is a part of X, never X itself, so the
// whole-variable exemption does not apply.
func PackageVar(info *types.Info, init *types.Initializer) (n ast.Node, msg string, ok bool) {
	if len(init.Lhs) != 1 {
		return nil, "", false
	}
	c := checker{info}
	var found ast.Expr
	var walk func(e ast.Expr)
	walk = func(e ast.Expr) {
		if found != nil {
			return
		}
		e = ast.Unparen(e)
		if conv, ok := c.conversion(e); ok {
			walk(conv.Args[0])
			return
		}
		if c.inlinableCall(e) {
			found = e
			return
		}
		lit, ok := e.(*ast.CompositeLit)
		if !ok {
			return
		}
		if _, isMap := under(info.TypeOf(lit)).(*types.Map); isMap {
			return // map entries are copied into the map's own storage
		}
		for _, elt := range lit.Elts {
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				elt = kv.Value
			}
			v := ast.Unparen(elt)
			if _, isLit := v.(*ast.CompositeLit); isLit {
				walk(v)
				continue
			}
			if t := info.TypeOf(v); t != nil && mayBeMoved(t) && c.isSource(v) {
				found = v
				return
			}
			walk(v)
		}
	}
	walk(init.Rhs)
	if found == nil {
		return nil, "", false
	}
	if c.inlinableCall(found) {
		return found, report("call %s in the initializer of package variable %s: gc may inline it and build "+
			"its result, of type %s, in place, copying parts of it from memory",
			types.ExprString(found), init.Lhs[0].Name(), info.TypeOf(found)), true
	}
	return found, report("copy of %s into part of package variable %s (%s), which gc builds in place",
		info.TypeOf(found), init.Lhs[0].Name(), types.ExprString(found)), true
}

// inlinableCall reports whether e is a call that gc may inline and build in
// place in a package variable (staticinit's staticAssignInlinedCall: a callee
// whose body is a single return, with arguments free of side effects; the
// callee may be in any package, so its body is not examined), and whose
// result contains, by value, a part two views of which may partially overlap.
// A conversion or a builtin call is not such a call; neither is a call whose
// result is a pointer, built into a fresh object.
func (c checker) inlinableCall(e ast.Expr) bool {
	call, ok := ast.Unparen(e).(*ast.CallExpr)
	if !ok {
		return false
	}
	if _, isConv := c.conversion(call); isConv {
		return false
	}
	if id, ok := ast.Unparen(call.Fun).(*ast.Ident); ok {
		if _, isBuiltin := c.info.Uses[id].(*types.Builtin); isBuiltin {
			return false
		}
	}
	t := c.info.TypeOf(call)
	return t != nil && containsMovable(t)
}

// containsMovable reports whether a value of type t contains, by value (not
// through a pointer, slice, map, channel, function or interface), a part of a
// type mayBeMoved accepts.
func containsMovable(t types.Type) bool {
	if mayBeMoved(t) {
		return true
	}
	switch u := under(t).(type) {
	case *types.Struct:
		for i := range u.NumFields() {
			if containsMovable(u.Field(i).Type()) {
				return true
			}
		}
	case *types.Tuple:
		for i := range u.Len() {
			if containsMovable(u.At(i).Type()) {
				return true
			}
		}
	}
	return false
}

func report(format string, args ...any) string {
	return Prefix + fmt.Sprintf(format, args...) +
		"; the semantics copies by value, but gc does not when the two sides partially overlap" +
		" (docs/design/unsafe-memory.md, R4); copy through a local variable instead"
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

// mayBeMoved reports whether two views of type t may partially overlap, so
// that gc's Move of a t can differ from the semantics' copy by value: any
// array type, a pointer-free struct type, or a type parameter. This is a
// deliberate superset of the types with such views:
//   - plain types (design R1), viewed with unsafe; pointer-free covers them,
//     so that the guard need not agree with the semantics on padding, blank
//     fields, zero size or floats;
//   - arrays of any element type, viewed in safe Go by converting overlapping
//     slices to array pointers, which gc copies with a Move rather than
//     memmove when the two sides' array types differ only in being named.
//
// A struct with pointers has neither: safe Go cannot view a struct over a
// slice, and the semantics makes every unsafe view of a non-plain type stuck
// (R3). A scalar is one load and one store, not a Move.
func mayBeMoved(t types.Type) bool {
	switch under(t).(type) {
	case nil, *types.Array:
		return true
	case *types.Struct:
		return pointerFree(t)
	}
	return false
}

// pointerFree reports whether t contains no pointer, unsafe.Pointer, slice,
// string, map, channel, function or interface (a type parameter may be
// instantiated to a type that does not).
func pointerFree(t types.Type) bool {
	switch u := under(t).(type) {
	case nil:
		return true
	case *types.Basic:
		return u.Info()&(types.IsInteger|types.IsFloat|types.IsComplex|types.IsBoolean) != 0
	case *types.Array:
		return pointerFree(u.Elem())
	case *types.Struct:
		for i := range u.NumFields() {
			if !pointerFree(u.Field(i).Type()) {
				return false
			}
		}
		return true
	}
	return false
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
func (c checker) isSource(rhs ast.Expr) bool {
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
// exactly its type's size (design R1), so no other view of its type can
// partially overlap it without leaving the block, which the semantics makes
// stuck (R3).
func (c checker) isPlace(e ast.Expr) bool {
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

// addressable reports whether e is addressable: a variable, or a place.
func (c checker) addressable(e ast.Expr) bool {
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

// sameBase reports whether lhs and rhs have the same base, which cannot
// change during the statement. Each place is a base followed by a path of
// steps that stay inside one object: direct field selections, indexing of an
// array value, and value-preserving conversions. The base is what is left: a
// whole variable, or the operand X of the first step that leaves the object
// (*X, a field through the pointer X, X[i] on a slice or a pointer to an
// array). Two places with the same base lie in one object, whose layout is a
// tree, so they are disjoint or the same place, and a Move is correct on both:
// data[i], data[j] = data[j], data[i] (sort's swap), p.X = p.Y, and
// p.next.A = p.next.B. Two different bases, such as the loaded pointers of
// *pr.y = *pr.x, can point at overlapping views.
func (c checker) sameBase(lhs, rhs ast.Expr) bool {
	l, okL := c.base(lhs)
	r, okR := c.base(rhs)
	return okL && okR && types.ExprString(l) == types.ExprString(r)
}

// base returns e's base (see sameBase). It reports false if the base or an
// index on the path could change memory or the base's value.
func (c checker) base(e ast.Expr) (ast.Expr, bool) {
	for {
		e = ast.Unparen(e)
		switch x := e.(type) {
		case *ast.StarExpr:
			return x.X, c.callFree(x.X)
		case *ast.SelectorExpr:
			sel := c.info.Selections[x]
			if sel == nil || sel.Kind() != types.FieldVal {
				break // pkg.V: a whole variable
			}
			if !sel.Indirect() {
				e = x.X // through embedded structs, not pointers
				continue
			}
			// The selection dereferences a pointer. Only when that pointer is
			// x.X itself (one step, no embedding) is x.X the base; a
			// promoted field reached through an embedded pointer has a loaded
			// pointer as its base, which this function does not name.
			if _, isPtr := under(c.info.TypeOf(x.X)).(*types.Pointer); isPtr && len(sel.Index()) == 1 {
				return x.X, c.callFree(x.X)
			}
			return nil, false
		case *ast.IndexExpr:
			if !c.callFree(x.Index) {
				return nil, false
			}
			switch under(c.info.TypeOf(x.X)).(type) {
			case *types.Array:
				e = x.X
				continue
			case *types.Slice, *types.Pointer:
				return x.X, c.callFree(x.X)
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

// callFree reports whether evaluating e cannot change memory and its text
// (types.ExprString, which abbreviates literals) determines it: it contains no
// call other than a conversion or len/cap, no receive, and no function or
// composite literal.
func (c checker) callFree(e ast.Expr) bool {
	free := true
	ast.Inspect(e, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit, *ast.CompositeLit:
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

// conversion returns e as a type conversion, if it is one.
func (c checker) conversion(e ast.Expr) (*ast.CallExpr, bool) {
	call, ok := ast.Unparen(e).(*ast.CallExpr)
	if !ok || len(call.Args) != 1 {
		return nil, false
	}
	tv, ok := c.info.Types[call.Fun]
	return call, ok && tv.IsType()
}
