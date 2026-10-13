// Package order fixes the evaluation order of Go statements.
//
// The Go spec orders the calls, method calls and communication operations of
// a statement (left to right), but not the other reads of its operands
// relative to them ("Order of evaluation"): in `x + f()` the read of x may
// happen before or after f runs, and compilers differ (gc changes its answer
// under -race). Perennial fixes one order, the same for verification and for
// compilation:
//
//	Within a statement, its events (calls, receives) run first, in lexical
//	left-to-right order, each after the evaluation of its own operands; then
//	the rest of the statement is evaluated and its assignments are carried
//	out.
//
// Rewrite implements that order by rewriting a statement into a sequence of
// statements in normal form (IsNormal): each has at most one event, and
// nothing outside that event's subtree reads state the event could change.
// Every order the spec allows gives the same result on a statement in normal
// form, so any compiler compiles it to the behaviour that goose translates.
// Statements already in normal form are left alone.
//
// The rewriter is not trusted: goose checks that what it translates is in
// normal form (CheckFile), and a binary is compiled from the same rewritten
// source by cmd/perennial-order (`go build -toolexec`).
package order

import (
	"go/ast"
	"go/token"
	"go/types"
)

// pure builtins: no effect, and no order constraint beyond their operands.
var pureBuiltins = map[string]bool{
	"len": true, "cap": true, "make": true, "new": true, "complex": true,
	"real": true, "imag": true, "min": true, "max": true,
	// package unsafe
	"Sizeof": true, "Alignof": true, "Offsetof": true, "Add": true,
	"Slice": true, "String": true, "StringData": true, "SliceData": true,
}

// analysis holds the facts about one file that the normal form needs.
type analysis struct {
	info *types.Info
	// unsafeVars are the local variables whose address is taken or that a
	// function literal other than the declaring one refers to: a call can
	// change them. Package-level variables are never safe.
	unsafeVars map[*types.Var]bool
	// localVars are the variables declared inside a function.
	localVars map[*types.Var]bool
}

func newAnalysis(info *types.Info, file *ast.File) *analysis {
	a := &analysis{info: info, unsafeVars: map[*types.Var]bool{}, localVars: map[*types.Var]bool{}}
	// owner[v] is the innermost function (FuncDecl or FuncLit) declaring v.
	owner := map[*types.Var]ast.Node{}
	var stack []ast.Node
	ast.Inspect(file, func(n ast.Node) bool {
		if n == nil {
			stack = stack[:len(stack)-1]
			return true
		}
		switch n.(type) {
		case *ast.FuncDecl, *ast.FuncLit:
			stack = append(stack, n)
			return true
		}
		stack = append(stack, nil)
		fn := enclosingFunc(stack)
		switch n := n.(type) {
		case *ast.Ident:
			if v, ok := a.info.Defs[n].(*types.Var); ok && fn != nil && !v.IsField() {
				owner[v] = fn
				a.localVars[v] = true
			}
			if v, ok := a.info.Uses[n].(*types.Var); ok {
				if o, ok := owner[v]; ok && o != fn {
					a.unsafeVars[v] = true // captured by a function literal
				}
			}
		case *ast.UnaryExpr:
			if n.Op == token.AND {
				a.markAddressed(n.X)
			}
		case *ast.SliceExpr:
			if _, ok := a.under(n.X).(*types.Array); ok {
				a.markAddressed(n.X) // slicing an array takes its address
			}
		case *ast.SelectorExpr:
			if sel := a.info.Selections[n]; sel != nil && sel.Kind() != types.FieldVal {
				if sig, ok := sel.Obj().Type().(*types.Signature); ok && sig.Recv() != nil {
					if _, ptrRecv := sig.Recv().Type().Underlying().(*types.Pointer); ptrRecv {
						if _, ptrX := a.under(n.X).(*types.Pointer); !ptrX {
							a.markAddressed(n.X) // x.M with M on *T: &x
						}
					}
				}
			}
		}
		return true
	})
	// a variable used in a function other than its declaring one, before
	// its declaration was seen (not possible in Go) is not handled; uses
	// are always after definitions in source order.
	return a
}

func enclosingFunc(stack []ast.Node) ast.Node {
	for i := len(stack) - 1; i >= 0; i-- {
		if stack[i] != nil {
			return stack[i]
		}
	}
	return nil
}

func (a *analysis) under(e ast.Expr) types.Type {
	t := a.info.TypeOf(e)
	if t == nil {
		return nil
	}
	return t.Underlying()
}

// markAddressed marks the variable at the root of the addressable operand e
// (x, x.f, x[i] for an array x) as address-taken.
func (a *analysis) markAddressed(e ast.Expr) {
	for {
		switch x := e.(type) {
		case *ast.ParenExpr:
			e = x.X
			continue
		case *ast.Ident:
			if v, ok := a.info.Uses[x].(*types.Var); ok {
				a.unsafeVars[v] = true
			}
			if v, ok := a.info.Defs[x].(*types.Var); ok {
				a.unsafeVars[v] = true
			}
			return
		case *ast.SelectorExpr:
			sel := a.info.Selections[x]
			if sel == nil || sel.Kind() != types.FieldVal || sel.Indirect() {
				return
			}
			if _, ptr := a.under(x.X).(*types.Pointer); ptr {
				return
			}
			e = x.X
			continue
		case *ast.IndexExpr:
			if _, ok := a.under(x.X).(*types.Array); ok {
				e = x.X
				continue
			}
			return
		case *ast.CompositeLit:
			return
		default:
			return
		}
	}
}

// safeVar reports whether reading v cannot be affected by a call: v is a
// local variable that is never address-taken nor captured.
func (a *analysis) safeVar(v *types.Var) bool {
	return a.localVars[v] && !a.unsafeVars[v]
}

// isConversion reports whether call is a type conversion.
func (a *analysis) isConversion(call *ast.CallExpr) bool {
	tv, ok := a.info.Types[call.Fun]
	return ok && tv.IsType()
}

// builtinName is the name of the builtin call calls, or "".
func (a *analysis) builtinName(call *ast.CallExpr) string {
	fun := ast.Unparen(call.Fun)
	var id *ast.Ident
	switch f := fun.(type) {
	case *ast.Ident:
		id = f
	case *ast.SelectorExpr:
		id = f.Sel
	default:
		return ""
	}
	if b, ok := a.info.Uses[id].(*types.Builtin); ok {
		return b.Name()
	}
	return ""
}

// isEvent reports whether e is an event: a call that is not a conversion or a
// pure builtin, or a receive.
func (a *analysis) isEvent(e ast.Expr) bool {
	switch e := e.(type) {
	case *ast.CallExpr:
		if a.isConversion(e) {
			return false
		}
		if b := a.builtinName(e); b != "" {
			return !pureBuiltins[b]
		}
		return true
	case *ast.UnaryExpr:
		return e.Op == token.ARROW
	}
	return false
}

// events lists the events in n (not inside function literals), in the order
// they run: post-order, left to right.
func (a *analysis) events(n ast.Node) []ast.Expr {
	var evs []ast.Expr
	var rec func(n ast.Node)
	rec = func(n ast.Node) {
		if _, ok := n.(*ast.FuncLit); ok {
			return
		}
		ast.Inspect(n, func(m ast.Node) bool {
			if m == nil {
				return false
			}
			if m != n {
				if ex, ok := m.(ast.Expr); ok {
					rec(ex)
					return false
				}
			}
			return true
		})
		if ex, ok := n.(ast.Expr); ok && a.isEvent(ex) {
			evs = append(evs, ex)
		}
	}
	rec(n)
	return evs
}

// sharedReads lists the nodes of n that read state a call could change: a
// variable other than a safe local, through a pointer, a slice or map
// element, or a channel's state. Address computations (&x.f, &a[i]) read only
// their operands.
func (a *analysis) sharedReads(n ast.Node) []ast.Node {
	var reads []ast.Node
	var value, addr func(e ast.Expr)
	children := func(e ast.Node) {
		ast.Inspect(e, func(m ast.Node) bool {
			if m == nil || m == e {
				return m == e
			}
			if ex, ok := m.(ast.Expr); ok {
				value(ex)
			}
			return false
		})
	}
	// addr evaluates the addressable operand e without reading it.
	addr = func(e ast.Expr) {
		switch x := e.(type) {
		case *ast.ParenExpr:
			addr(x.X)
		case *ast.Ident:
		case *ast.SelectorExpr:
			if sel := a.info.Selections[x]; sel != nil && sel.Kind() == types.FieldVal {
				if _, ptr := a.under(x.X).(*types.Pointer); ptr || sel.Indirect() {
					value(x.X) // the pointer is read, not the field
				} else {
					addr(x.X)
				}
				return
			}
			value(e)
		case *ast.IndexExpr:
			switch a.under(x.X).(type) {
			case *types.Array:
				addr(x.X)
			default:
				value(x.X)
			}
			value(x.Index)
		case *ast.StarExpr:
			value(x.X)
		default:
			value(e)
		}
	}
	value = func(e ast.Expr) {
		switch x := e.(type) {
		case *ast.FuncLit:
			return
		case *ast.UnaryExpr:
			if x.Op == token.AND {
				addr(x.X)
				return
			}
		case *ast.SliceExpr:
			if _, ok := a.under(x.X).(*types.Array); ok {
				addr(x.X) // slicing an array reads no element
				for _, i := range []ast.Expr{x.Low, x.High, x.Max} {
					if i != nil {
						value(i)
					}
				}
				return
			}
		case *ast.Ident:
			if v, ok := a.info.Uses[x].(*types.Var); ok && !v.IsField() && !a.safeVar(v) {
				reads = append(reads, x)
			}
			return
		case *ast.StarExpr:
			if tv, ok := a.info.Types[x]; ok && !tv.IsType() {
				reads = append(reads, x)
			}
		case *ast.IndexExpr:
			switch a.under(x.X).(type) {
			case *types.Slice, *types.Map, *types.Pointer:
				reads = append(reads, x)
			}
		case *ast.SelectorExpr:
			if sel := a.info.Selections[x]; sel != nil {
				if a.selectionReads(sel, x) {
					reads = append(reads, x)
				}
				if a.implicitAddr(sel, x) {
					addr(x.X) // x.M with M on *T takes &x
					return
				}
			}
		case *ast.CallExpr:
			if b := a.builtinName(x); (b == "len" || b == "cap") && len(x.Args) == 1 {
				if _, ch := a.under(x.Args[0]).(*types.Chan); ch {
					reads = append(reads, x)
				}
			}
		}
		children(e)
	}
	if e, ok := n.(ast.Expr); ok {
		value(e)
	} else {
		children(n)
	}
	return reads
}

// selectionReads reports whether the selection x.f reads memory beyond x: a
// field through a pointer, or a method with a value receiver selected through
// a pointer (which copies *x).
func (a *analysis) selectionReads(sel *types.Selection, x *ast.SelectorExpr) bool {
	_, ptrX := a.under(x.X).(*types.Pointer)
	if sel.Kind() == types.FieldVal {
		return ptrX || sel.Indirect()
	}
	sig, ok := sel.Obj().Type().(*types.Signature)
	if !ok || sig.Recv() == nil {
		return false
	}
	if _, ptrRecv := sig.Recv().Type().Underlying().(*types.Pointer); ptrRecv {
		return false
	}
	if _, isIface := sig.Recv().Type().Underlying().(*types.Interface); isIface {
		return false
	}
	return ptrX || sel.Indirect()
}

// implicitAddr reports whether the method selection x.M takes x's address
// (M has a pointer receiver and x is not a pointer).
func (a *analysis) implicitAddr(sel *types.Selection, x *ast.SelectorExpr) bool {
	if sel.Kind() == types.FieldVal {
		return false
	}
	sig, ok := sel.Obj().Type().(*types.Signature)
	if !ok || sig.Recv() == nil {
		return false
	}
	_, ptrRecv := sig.Recv().Type().Underlying().(*types.Pointer)
	_, ptrX := a.under(x.X).(*types.Pointer)
	return ptrRecv && !ptrX
}

func contains(outer, inner ast.Node) bool {
	return outer.Pos() <= inner.Pos() && inner.End() <= outer.End()
}

// unitNormal reports whether one evaluation unit (expressions evaluated left
// to right) is in normal form: every shared read is ordered with respect to
// every event by the spec, so that all orders the spec allows agree. A read r
// and an event e are ordered when one contains the other (an operand is
// evaluated before its operation), when r is inside an event that runs before
// e, or when r contains an event that runs at or after e (calls and receives
// run in lexical left-to-right order, operands first).
func (a *analysis) unitNormal(exprs []ast.Expr) bool {
	var evs []ast.Expr
	var reads []ast.Node
	for _, e := range exprs {
		evs = append(evs, a.events(e)...)
		reads = append(reads, a.sharedReads(e)...)
	}
	if len(evs) == 0 || len(reads) == 0 {
		return true
	}
	for _, r := range reads {
		for j, e := range evs {
			if contains(r, e) || contains(e, r) {
				continue
			}
			ordered := false
			for i, e2 := range evs {
				if (i < j && contains(e2, r)) || (i >= j && contains(r, e2)) {
					ordered = true
					break
				}
			}
			if !ordered {
				return false
			}
		}
	}
	return true
}
