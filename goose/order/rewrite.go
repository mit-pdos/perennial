package order

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"sort"
	"strconv"
	"strings"
)

// edit replaces src[lo:hi] by text.
type edit struct {
	lo, hi int
	text   string
}

type rewriter struct {
	fset *token.FileSet
	tf   *token.File
	a    *analysis
	file *ast.File
	pkg  *types.Package
	src  []byte

	edits  []edit // sorted by lo, non-overlapping
	prefix string // of temporaries
	n      int
	pre    []string // hoisted statements of the expression being rewritten
	err    error
	fnBody *ast.BlockStmt // the body of the function being rewritten (label scope)
}

// Rewrite rewrites the statements of file that are not in normal form into
// sequences of statements that are, implementing Perennial's evaluation order
// (see the package comment). src is the file's source and info its type
// information. It returns the new source (with //line directives mapping every
// position to the original one) and whether anything changed.
func Rewrite(fset *token.FileSet, pkg *types.Package, info *types.Info, file *ast.File, src []byte) ([]byte, bool, error) {
	r := &rewriter{fset: fset, tf: fset.File(file.Pos()), a: newAnalysis(info, file), file: file, pkg: pkg, src: src}
	r.prefix = r.freshPrefix()
	for _, d := range file.Decls {
		switch d := d.(type) {
		case *ast.FuncDecl:
			if d.Body != nil {
				r.fnBody = d.Body
				r.block(d.Body)
			}
		case *ast.GenDecl:
			if d.Tok == token.VAR {
				for _, sp := range d.Specs {
					r.funcLits(sp)
					r.pkgVar(sp.(*ast.ValueSpec))
				}
			}
		}
	}
	if r.err != nil {
		return nil, false, r.err
	}
	if len(r.edits) == 0 {
		return src, false, nil
	}
	pos := r.fset.PositionFor(file.Package, true)
	var b strings.Builder
	// Positions before the package clause (comments, build constraints)
	// carry no code; map the start of the file to its first line.
	fmt.Fprintf(&b, "//line %s:1:1\n", r.fset.PositionFor(r.tf.Pos(0), true).Filename)
	_ = pos
	b.WriteString(r.render(0, len(src)))
	return []byte(b.String()), true, nil
}

func (r *rewriter) fail(n ast.Node, format string, args ...any) {
	if r.err == nil {
		r.err = fmt.Errorf("%v: %s", r.fset.Position(n.Pos()), fmt.Sprintf(format, args...))
	}
}

func (r *rewriter) freshPrefix() string {
	prefix := "_order"
	for {
		clash := false
		ast.Inspect(r.file, func(n ast.Node) bool {
			if id, ok := n.(*ast.Ident); ok && strings.HasPrefix(id.Name, prefix) {
				clash = true
			}
			return !clash
		})
		if !clash {
			return prefix
		}
		prefix += "_"
	}
}

func (r *rewriter) temp() string {
	r.n++
	return r.prefix + strconv.Itoa(r.n)
}

func (r *rewriter) off(p token.Pos) int { return r.tf.Offset(p) }

// dir is a line directive giving the text that follows the position of p in
// the original file.
func (r *rewriter) dir(p token.Pos) string {
	pos := r.fset.PositionFor(p, true)
	return fmt.Sprintf("/*line %s:%d:%d*/", pos.Filename, pos.Line, pos.Column)
}

func (r *rewriter) dirOff(off int) string { return r.dir(r.tf.Pos(off)) }

// addEdit replaces src[lo:hi]; the edits inside it are part of text.
func (r *rewriter) addEdit(lo, hi int, text string) {
	var out []edit
	for _, e := range r.edits {
		if lo <= e.lo && e.hi <= hi {
			continue
		}
		if e.lo < hi && lo < e.hi {
			r.err = fmt.Errorf("order: overlapping edits at %v", r.fset.Position(r.tf.Pos(lo)))
		}
		out = append(out, e)
	}
	out = append(out, edit{lo, hi, text})
	sort.Slice(out, func(i, j int) bool { return out[i].lo < out[j].lo })
	r.edits = out
}

func (r *rewriter) render(lo, hi int) string {
	var b strings.Builder
	pos := lo
	for _, e := range r.edits {
		if e.lo >= lo && e.hi <= hi && e.lo >= pos {
			b.Write(r.src[pos:e.lo])
			b.WriteString(e.text)
			pos = e.hi
		}
	}
	b.Write(r.src[pos:hi])
	return b.String()
}

func (r *rewriter) text(n ast.Node) string { return r.render(r.off(n.Pos()), r.off(n.End())) }

// frag is n's (rewritten) text, preceded by a directive giving its position.
func (r *rewriter) frag(n ast.Node) string { return r.dir(n.Pos()) + r.text(n) }

// replace replaces n by text, followed by a directive giving the position of
// what follows n.
func (r *rewriter) replace(n ast.Node, text string) {
	r.addEdit(r.off(n.Pos()), r.off(n.End()), text+r.dirOff(r.off(n.End())))
}

// funcLits rewrites the bodies of the function literals in n.
func (r *rewriter) funcLits(n ast.Node) {
	if n == nil {
		return
	}
	ast.Inspect(n, func(m ast.Node) bool {
		if fl, ok := m.(*ast.FuncLit); ok {
			saved := r.fnBody
			r.fnBody = fl.Body
			r.block(fl.Body)
			r.fnBody = saved
			return false
		}
		return true
	})
}

func (r *rewriter) block(b *ast.BlockStmt) {
	for _, s := range b.List {
		r.stmt(s, nil)
	}
}

func (r *rewriter) stmtList(l []ast.Stmt) {
	for _, s := range l {
		r.stmt(s, nil)
	}
}

// stmt rewrites s (labeled by label, if not nil) and the statements in it.
func (r *rewriter) stmt(s ast.Stmt, label *ast.LabeledStmt) {
	switch s := s.(type) {
	case *ast.BlockStmt:
		r.block(s)
		return
	case *ast.LabeledStmt:
		r.stmt(s.Stmt, s)
		return
	case *ast.IfStmt, *ast.ForStmt, *ast.RangeStmt, *ast.SwitchStmt, *ast.TypeSwitchStmt, *ast.SelectStmt:
		// A label on a statement that needs statements before it: a goto
		// keeps the label outside the new block; break and continue target
		// a fresh label on the statement inside it.
		var gotos, branches bool
		newLabel := ""
		if label != nil && !r.a.headerNormal(s) && r.needsPre(s) {
			gotos, branches = r.labelUses(label.Label.Name)
			if branches {
				r.n++
				newLabel = r.prefix + "L" + strconv.Itoa(r.n)
				r.renameBranches(s, label.Label.Name, newLabel)
			}
		}
		pre, text, changed := r.compound(s)
		if !changed {
			return
		}
		if pre == "" {
			r.replace(s, text)
			return
		}
		if label == nil {
			r.replace(s, "{ "+pre+text+" }")
			return
		}
		out := ""
		if gotos {
			out = r.dir(label.Pos()) + label.Label.Name + ": "
		}
		out += "{ " + pre
		if newLabel != "" {
			out += newLabel + ": "
		}
		r.replace(label, out+text+" }")
		return
	case *ast.CaseClause, *ast.CommClause:
		return // handled by their statement
	}
	r.funcLits(s)
	if r.a.headerNormal(s) {
		return
	}
	pre, res, declaring := r.simple(s)
	if declaring {
		r.replace(s, pre+res)
	} else {
		r.replace(s, "{ "+pre+res+" }")
	}
}

// needsPre reports whether rewriting the compound statement s (whose header
// is not in normal form) puts statements before it.
func (r *rewriter) needsPre(s ast.Stmt) bool {
	switch s := s.(type) {
	case *ast.ForStmt:
		return s.Init != nil && !r.a.headerNormal(s.Init)
	case *ast.RangeStmt:
		return !r.a.unitNormal([]ast.Expr{s.X})
	case *ast.SwitchStmt:
		return r.switchNeedsPre(s)
	}
	return true
}

// labelUses reports whether the label is the target of a goto, and of a break
// or continue, in the current function.
func (r *rewriter) labelUses(name string) (gotos, branches bool) {
	ast.Inspect(r.fnBody, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			return false
		case *ast.BranchStmt:
			if n.Label != nil && n.Label.Name == name {
				if n.Tok == token.GOTO {
					gotos = true
				} else {
					branches = true
				}
			}
		}
		return true
	})
	return
}

// renameBranches renames the label of the break and continue statements in s
// that target name.
func (r *rewriter) renameBranches(s ast.Stmt, name, newName string) {
	ast.Inspect(s, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncLit:
			return false
		case *ast.BranchStmt:
			if n.Label != nil && n.Label.Name == name && n.Tok != token.GOTO {
				r.addEdit(r.off(n.Label.Pos()), r.off(n.Label.End()), newName)
			}
		}
		return true
	})
}

// hoisting collects the statements that hoisting the events of f emits.
func (r *rewriter) hoisting(f func()) string {
	saved := r.pre
	r.pre = nil
	f()
	out := strings.Join(r.pre, "")
	r.pre = saved
	return out
}

// simple rewrites a simple statement not in normal form: the hoisted
// statements, the rest of s (with its position), and whether s declares
// variables in its scope (and so cannot be put in a block).
func (r *rewriter) simple(s ast.Stmt) (pre, res string, declaring bool) {
	pre = r.hoisting(func() {
		switch s := s.(type) {
		case *ast.ExprStmt:
			r.hoistChildren(ast.Unparen(s.X)) // the call or receive stays
		case *ast.SendStmt:
			r.hoistExpr(s.Chan)
			r.hoistExpr(s.Value)
		case *ast.IncDecStmt:
			r.hoistExpr(s.X)
		case *ast.AssignStmt:
			declaring = s.Tok == token.DEFINE
			if s.Tok != token.DEFINE {
				for _, l := range s.Lhs {
					r.hoistExpr(l)
				}
			}
			if recv, ok := ast.Unparen(s.Rhs[0]).(*ast.UnaryExpr); ok && recv.Op == token.ARROW && len(s.Lhs) == 2 && len(s.Rhs) == 1 {
				r.hoistChildren(recv)
				t1, t2 := r.temp(), r.temp()
				r.pre = append(r.pre, r.dir(recv.Pos())+t1+", "+t2+" := "+r.text(recv)+"; ")
				r.replace(s.Rhs[0], t1+", "+t2)
			} else {
				for _, e := range s.Rhs {
					r.hoistExpr(e)
				}
			}
		case *ast.ReturnStmt:
			for _, e := range s.Results {
				r.hoistExpr(e)
			}
		case *ast.GoStmt:
			r.hoistChildren(s.Call)
		case *ast.DeferStmt:
			r.hoistChildren(s.Call)
		case *ast.DeclStmt:
			declaring = true
			gd := s.Decl.(*ast.GenDecl)
			if len(gd.Specs) > 1 {
				return // below
			}
			for _, e := range gd.Specs[0].(*ast.ValueSpec).Values {
				r.hoistExpr(e)
			}
		default:
			r.fail(s, "order: unexpected statement %T", s)
		}
	})
	if ds, ok := s.(*ast.DeclStmt); ok && len(ds.Decl.(*ast.GenDecl).Specs) > 1 {
		// var ( a = e1; b = e2 ) is var a = e1; var b = e2, in order.
		res = ""
		for _, sp := range ds.Decl.(*ast.GenDecl).Specs {
			p := r.hoisting(func() {
				for _, e := range sp.(*ast.ValueSpec).Values {
					r.hoistExpr(e)
				}
			})
			res += p + r.dir(sp.Pos()) + "var " + r.text(sp) + "; "
		}
		return "", res, true
	}
	return pre, r.frag(s), declaring
}

// hoistExpr emits the events of e as statements binding temporaries, in the
// order they run, and replaces each by its temporary.
func (r *rewriter) hoistExpr(e ast.Expr) {
	switch x := e.(type) {
	case nil:
		return
	case *ast.FuncLit:
		return
	case *ast.BinaryExpr:
		if (x.Op == token.LAND || x.Op == token.LOR) && len(r.a.events(x.Y)) > 0 {
			r.shortCircuit(x)
			return
		}
	case *ast.CallExpr:
		// unsafe.Pointer(u) with u a uintptr from a call must stay one
		// expression (the unsafe.Pointer rules): hoist the conversion.
		if r.a.isConversion(x) && len(x.Args) == 1 && isUnsafePointer(r.a.info.TypeOf(x)) {
			if arg := ast.Unparen(x.Args[0]); r.a.isEvent(arg) {
				r.hoistChildren(arg)
				r.emitTemp(x)
				return
			}
		}
	}
	r.hoistChildren(e)
	if r.a.isEvent(e) {
		r.emitTemp(e)
	}
}

func isUnsafePointer(t types.Type) bool {
	b, ok := t.(*types.Basic)
	return ok && b.Kind() == types.UnsafePointer
}

// hoistChildren hoists the events in e's operands, in order.
func (r *rewriter) hoistChildren(e ast.Expr) {
	ast.Inspect(e, func(n ast.Node) bool {
		if n == nil || n == e {
			return n == e
		}
		if c, ok := n.(ast.Expr); ok {
			r.hoistExpr(c)
		}
		return false
	})
}

// emitTemp binds the event e (whose operands are hoisted) to temporaries.
func (r *rewriter) emitTemp(e ast.Expr) {
	n := 1
	if tup, ok := r.a.info.TypeOf(e).(*types.Tuple); ok {
		n = tup.Len()
	}
	if n == 0 {
		r.fail(e, "order: a call with no result inside an expression")
		return
	}
	var names []string
	for range n {
		names = append(names, r.temp())
	}
	ts := strings.Join(names, ", ")
	r.pre = append(r.pre, r.dir(e.Pos())+ts+" := "+r.text(e)+"; ")
	r.replace(e, ts)
}

// shortCircuit rewrites x && y (or x || y) where y has events into
//
//	var t T = x; if t { y's events; t = y }
//
// (if !t for ||), which evaluates y only when the operator does.
func (r *rewriter) shortCircuit(x *ast.BinaryExpr) {
	r.hoistExpr(x.X)
	typ := r.typeText(x, r.a.info.TypeOf(x))
	t := r.temp()
	r.pre = append(r.pre, r.dir(x.Pos())+"var "+t+" "+typ+" = "+r.text(x.X)+"; ")
	inner := r.hoisting(func() { r.hoistExpr(x.Y) })
	cond := t
	if x.Op == token.LOR {
		cond = "!" + t
	}
	r.pre = append(r.pre, "if "+cond+" { "+inner+r.dir(x.Y.Pos())+t+" = "+r.text(x.Y)+" }; ")
	r.replace(x, t)
}

// typeText is t written in the file's terms.
func (r *rewriter) typeText(n ast.Node, t types.Type) string {
	if b, ok := t.(*types.Basic); ok && b.Info()&types.IsUntyped != 0 {
		return types.Typ[types.Default(b).(*types.Basic).Kind()].Name()
	}
	ok := true
	s := types.TypeString(t, func(p *types.Package) string {
		if p == r.pkg {
			return ""
		}
		for _, imp := range r.file.Imports {
			pn := r.a.info.PkgNameOf(imp)
			if pn == nil || pn.Imported() != p {
				continue
			}
			if pn.Name() == "." {
				return ""
			}
			if pn.Name() != "_" {
				return pn.Name()
			}
		}
		ok = false
		return p.Name()
	})
	if !ok {
		r.fail(n, "order: cannot name type %v here", t)
	}
	return s
}

// compound rewrites the header of a compound statement not in normal form:
// the statements to run before it, and the statement itself.
func (r *rewriter) compound(s ast.Stmt) (pre, text string, changed bool) {
	switch s := s.(type) {
	case *ast.IfStmt:
		r.funcLits(s.Init)
		r.funcLits(s.Cond)
		r.block(s.Body)
		if s.Else != nil {
			r.stmt(s.Else, nil)
		}
		if r.a.headerNormal(s) {
			return "", "", false
		}
		pre = r.initPre(s.Init)
		pre += r.hoisting(func() { r.hoistExpr(s.Cond) })
		text = r.dir(s.Pos()) + "if " + r.frag(s.Cond) + " " + r.frag(s.Body)
		if s.Else != nil {
			text += " else " + r.frag(s.Else)
		}
		return pre, text, true
	case *ast.ForStmt:
		r.funcLits(s.Init)
		r.funcLits(s.Cond)
		r.funcLits(s.Post)
		r.block(s.Body)
		if r.a.headerNormal(s) {
			return "", "", false
		}
		if s.Post != nil && !r.a.headerNormal(s.Post) {
			r.fail(s.Post, "order: a for statement's post statement not in normal form")
			return "", "", false
		}
		init := ""
		if s.Init != nil {
			if r.a.headerNormal(s.Init) {
				init = r.frag(s.Init)
			} else {
				p, res, _ := r.simple(s.Init)
				pre, init = p, res
			}
		}
		cond := ""
		body := r.frag(s.Body)
		if s.Cond != nil {
			if r.a.unitNormal([]ast.Expr{s.Cond}) {
				cond = r.frag(s.Cond)
			} else {
				condPre := r.hoisting(func() { r.hoistExpr(s.Cond) })
				lb := r.off(s.Body.Lbrace) + 1
				body = r.dir(s.Body.Lbrace) + "{ " + condPre + "if !(" + r.frag(s.Cond) + ") { break }; " +
					r.dirOff(lb) + r.render(lb, r.off(s.Body.End()))
			}
		}
		post := ""
		if s.Post != nil {
			post = r.frag(s.Post)
		}
		text = r.dir(s.Pos()) + "for " + init + "; " + cond + "; " + post + " " + body
		return pre, text, true
	case *ast.RangeStmt:
		r.funcLits(s.X)
		r.block(s.Body)
		if r.a.headerNormal(s) {
			return "", "", false
		}
		if !r.a.unitNormal([]ast.Expr{s.X}) {
			pre = r.hoisting(func() { r.hoistExpr(s.X) })
		}
		if s.Tok == token.ASSIGN && !r.a.headerNormal(&ast.RangeStmt{X: &ast.Ident{}, Key: s.Key, Value: s.Value, Tok: s.Tok}) {
			r.fail(s, "order: a range statement assigning to operands not in normal form")
		}
		hdr := r.render(r.off(s.Pos()), r.off(s.X.Pos()))
		text = r.dir(s.Pos()) + hdr + r.frag(s.X) + " " + r.frag(s.Body)
		return pre, text, true
	case *ast.SwitchStmt:
		r.funcLits(s.Init)
		r.funcLits(s.Tag)
		r.clauses(s.Body)
		if r.a.headerNormal(s) {
			return "", "", false
		}
		head := ""
		tag := ""
		if r.switchNeedsPre(s) {
			pre = r.initPre(s.Init)
		} else if s.Init != nil {
			head = r.frag(s.Init) + "; "
		}
		if s.Tag != nil {
			if !r.a.unitNormal([]ast.Expr{s.Tag}) {
				pre += r.hoisting(func() { r.hoistExpr(s.Tag) })
			}
			tag = r.frag(s.Tag)
			if !r.a.casesNormal(s) {
				// the cases are split into nested switches: evaluate the
				// tag once
				t := r.temp()
				pre += r.dir(s.Tag.Pos()) + t + " := " + tag + "; "
				tag = t
			}
		}
		var clauses []*ast.CaseClause
		for _, c := range s.Body.List {
			clauses = append(clauses, c.(*ast.CaseClause))
		}
		text = r.dir(s.Pos()) + r.switchText(head, tag, clauses, map[*ast.CaseClause]bool{})
		return pre, text, true
	case *ast.TypeSwitchStmt:
		r.funcLits(s.Init)
		r.funcLits(s.Assign)
		r.clauses(s.Body)
		if r.a.headerNormal(s) {
			return "", "", false
		}
		pre = r.initPre(s.Init)
		x := typeSwitchX(s)
		pre += r.hoisting(func() { r.hoistExpr(x) })
		text = r.dir(s.Pos()) + "switch " + r.frag(s.Assign) + " " + r.frag(s.Body)
		return pre, text, true
	case *ast.SelectStmt:
		for _, c := range s.Body.List {
			cc := c.(*ast.CommClause)
			r.funcLits(cc.Comm)
			r.stmtList(cc.Body)
		}
		if r.a.headerNormal(s) {
			return "", "", false
		}
		for _, u := range r.a.selectLhs(s) {
			if !r.a.unitNormal(u) {
				r.fail(s, "order: a select case assigning to operands not in normal form")
				return "", "", false
			}
		}
		pre = r.hoisting(func() {
			for _, e := range selectUnit(s) {
				r.hoistExpr(e)
			}
		})
		return pre, r.frag(s), true
	}
	return "", "", false
}

// switchNeedsPre reports whether rewriting the switch s puts statements
// before it: its init or tag is not in normal form, or its cases are and it
// has a tag (evaluated once into a temporary).
func (r *rewriter) switchNeedsPre(s *ast.SwitchStmt) bool {
	return (s.Init != nil && !r.a.headerNormal(s.Init)) ||
		(s.Tag != nil && (!r.a.unitNormal([]ast.Expr{s.Tag}) || !r.a.casesNormal(s)))
}

// switchText is a switch over the clauses (head is its init statement, tag
// its tag). The cases are evaluated in order until one matches, so a case
// expression not in normal form k splits the switch: the clauses before k,
// then a default clause that runs k's hoisted statements and a switch over
// the rest (including the original default clause). A break in an inner
// switch ends the whole construct, as in the original.
func (r *rewriter) switchText(head, tag string, clauses []*ast.CaseClause, split map[*ast.CaseClause]bool) string {
	k := -1
	for i, c := range clauses {
		if split[c] {
			continue // its first case is hoisted
		}
		for j, e := range c.List {
			_ = j
			if !r.a.unitNormal([]ast.Expr{e}) {
				if k < 0 {
					k = i
				}
			}
		}
		if k >= 0 {
			break
		}
	}
	open := "switch " + head + tag + " { "
	if k < 0 {
		out := open
		for _, c := range clauses {
			out += r.frag(c) + "; "
		}
		return out + "}"
	}
	if k > 0 && endsInFallthrough(clauses[k-1]) {
		r.fail(clauses[k], "order: fallthrough into a switch case expression not in normal form")
	}
	out := open
	var rest []*ast.CaseClause
	for _, c := range clauses[:k] {
		if c.List == nil {
			if endsInFallthrough(c) {
				r.fail(c, "order: fallthrough from a default clause before a case not in normal form")
			}
			rest = append(rest, c) // the default clause moves inside
			continue
		}
		out += r.frag(c) + "; "
	}
	if ck := clauses[k]; len(ck.List) > 1 {
		// case e0, e1, ...: evaluate e0, e1, ... in turn until one
		// matches, into m; then switch { case m: body; default: rest }.
		if endsInFallthrough(ck) {
			r.fail(ck, "order: fallthrough from a switch clause whose cases are not in normal form")
		}
		m := r.temp()
		match := ""
		for i, e := range ck.List {
			p := r.hoisting(func() { r.hoistExpr(e) })
			cmp := "bool(" + r.frag(e) + ")"
			if tag != "" {
				cmp = "(" + r.frag(e) + ") == " + tag
			}
			if i == 0 {
				match += p + "var " + m + " bool = " + cmp + "; "
			} else {
				match += "if !" + m + " { " + p + m + " = " + cmp + " }; "
			}
		}
		colon := r.off(ck.Colon) + 1
		body := r.dirOff(colon) + r.render(colon, r.off(ck.End()))
		rest = append(rest, clauses[k+1:]...)
		inner := "switch { case " + m + ":" + body + "; default: " + r.switchText("", tag, rest, split) + " }"
		return out + "default: " + match + inner + " }"
	}
	rest = append(rest, clauses[k:]...)
	pre := r.hoisting(func() { r.hoistExpr(clauses[k].List[0]) })
	split[clauses[k]] = true
	return out + "default: " + pre + r.switchText("", tag, rest, split) + " }"
}

func endsInFallthrough(c *ast.CaseClause) bool {
	if len(c.Body) == 0 {
		return false
	}
	b, ok := c.Body[len(c.Body)-1].(*ast.BranchStmt)
	return ok && b.Tok == token.FALLTHROUGH
}

func (r *rewriter) clauses(b *ast.BlockStmt) {
	for _, c := range b.List {
		cc := c.(*ast.CaseClause)
		for _, e := range cc.List {
			r.funcLits(e)
		}
		r.stmtList(cc.Body)
	}
}

// initPre is the init statement of an if or switch, moved before it (with its
// own hoisted statements).
func (r *rewriter) initPre(init ast.Stmt) string {
	if init == nil {
		return ""
	}
	if r.a.headerNormal(init) {
		return r.frag(init) + "; "
	}
	pre, res, _ := r.simple(init)
	return pre + res + "; "
}

// pkgVar rewrites a package-level variable declaration whose initializer is
// not in normal form into var x T = func() T { ...; return e }().
func (r *rewriter) pkgVar(sp *ast.ValueSpec) {
	if len(sp.Values) == 0 || r.a.unitNormal(sp.Values) {
		return
	}
	var types_ []string
	for _, n := range sp.Names {
		types_ = append(types_, r.typeText(n, r.a.info.TypeOf(n)))
	}
	pre := r.hoisting(func() {
		for _, e := range sp.Values {
			r.hoistExpr(e)
		}
	})
	var vals []string
	for _, e := range sp.Values {
		vals = append(vals, r.frag(e))
	}
	var names []string
	for _, n := range sp.Names {
		names = append(names, n.Name)
	}
	res := strings.Join(types_, ", ")
	if len(types_) > 1 {
		res = "(" + res + ")"
	}
	typ := ""
	if sp.Type != nil {
		typ = " " + r.text(sp.Type)
	}
	r.replace(sp, r.dir(sp.Pos())+strings.Join(names, ", ")+typ+" = func() "+res+" { "+pre+
		"return "+strings.Join(vals, ", ")+" }()")
}
