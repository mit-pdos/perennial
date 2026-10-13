package order

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"testing"
)

func check(t *testing.T, src string) (*token.FileSet, *ast.File, *types.Info) {
	t.Helper()
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "x.go", src, parser.ParseComments)
	if err != nil {
		t.Fatal(err)
	}
	info := &types.Info{Types: map[ast.Expr]types.TypeAndValue{}, Defs: map[*ast.Ident]types.Object{},
		Uses: map[*ast.Ident]types.Object{}, Selections: map[*ast.SelectorExpr]*types.Selection{}}
	conf := types.Config{Importer: importer.Default()}
	if _, err := conf.Check("p", fset, []*ast.File{f}, info); err != nil {
		t.Fatal(err)
	}
	return fset, f, info
}

// nonNormal lists the lines of the statements of src not in normal form.
func nonNormal(t *testing.T, src string) []int {
	fset, f, info := check(t, src)
	var lines []int
	for _, v := range CheckFile(info, f, nil) {
		lines = append(lines, fset.Position(v.Pos).Line)
	}
	return lines
}

func TestNormal(t *testing.T) {
	src := `package p

type G struct{ c []byte }

func (g G) ctrls() *G       { return &g }
func (g *G) match(b byte) int { return 0 }
func h2(x int) byte          { return 0 }

var global int
var gv G

func f() int { return 0 }

func ex(g G, hash int, a []int, i int, p *int) {
	_ = g.ctrls().match(h2(hash)) // 15: normal: g is read inside the first call
	_ = a[i] + f()                // 16: not normal
	_ = global + f()              // 17: not normal
	_ = i + f()                   // 18: normal: i is a safe local
	_ = f() + f()                 // 19: normal: calls are ordered
	_ = *p + f()                  // 20: not normal
	_ = g.ctrls().c[0]            // 20: normal: read of the call's result
	_ = f() + gv.match(0)         // 21: normal: &gv, not a read of gv
	q := &g                       // 22: g is now address-taken
	_ = q
}

func ex2(m map[int]int, b []byte, x, y int, arr [4]int, i int, v any) {
	_ = len(m) + f()        // 28: not normal: f may grow m
	_ = string(b) + "a"     // 29: normal: no event
	_ = len(string(b)) + f() // 30: not normal: f may change b's elements
	_ = x/y + f()           // 31: not normal: the division may panic
	_ = x/2 + f()           // 32: normal
	_ = arr[i] + f()        // 33: not normal: bounds check
	_ = arr[1] + f()        // 34: normal: checked statically
	_ = v.(int) + f()       // 35: not normal: the assertion may fail
	_ = x + f()             // 36: normal
}
`
	got := nonNormal(t, src)
	want := []int{16, 17, 20, 28, 30, 31, 33, 35}
	if len(got) != len(want) {
		t.Fatalf("got %v, want %v", got, want)
	}
	for i := range got {
		if got[i] != want[i] {
			t.Fatalf("got %v, want %v", got, want)
		}
	}
}

// Operations that can panic, and type parameters, which stand for any type in
// their type set.
func TestNormalPanics(t *testing.T) {
	src := `package p

import "unsafe"

type I interface{ M(...int) int }

func f() int { return 0 }
func h(...any) {}

func ex(n int, i I, p *int, k any) {
	h(make([]int, n), f())          // 11: not normal: make panics on n < 0
	h(make([]int, 3), f())          // 12: normal
	h(make(chan int, n), f())       // 13: not normal
	h(i.M, f())                     // 14: not normal: i.M panics on a nil i
	_ = i.M() + f()                 // 15: normal: i.M is read in the first call
	h(i.M(f()))                     // 16: not normal: i.M may be evaluated first
	h(I.M, f())                     // 17: normal: a method expression
	h(unsafe.Slice(p, n), f())      // 18: not normal
	h(map[any]int{k: 0}, f())       // 19: not normal: k may be unhashable
	h(map[int]int{n: 0}, f())       // 20: normal
}

type E struct{ v int }

func (e *E) N(...int) int { return 0 }

type S struct{ E }
type SP struct{ *E }

func ex3(k any, p *S, pa *[4]int, q *SP, e *E) {
	_ = map[any]int{k: 0, "x": f()} // 31: not normal: k is hashed as its entry is inserted
	_ = p.N(f())                    // 32: not normal: p.N is (&p.E).N, which reads *p
	h(&pa[2], f())                  // 33: not normal: nil check of pa
	q.v = f()                       // 34: not normal: q.E is read in phase 1
	e.v = f()                       // 35: normal
}

type Num interface{ ~int | ~uint }
type Arr interface{ ~[4]int }
type Bs interface{ ~[]byte }
type Ms interface{ ~map[int]int }

func gen[T Num, A Arr, B Bs, M Ms](x, y T, a A, b B, m M, u uint) {
	_ = x/y + T(f())           // 44: not normal: the division may panic
	_ = u<<y + uint(f())       // 45: not normal: y may be signed
	s := a[:]                  // 46: a is now address-taken
	h(a, f())                  // 47: not normal: f may change a through s
	h(string(b), f())          // 48: not normal: f may change b's elements
	h(len(m), f())             // 49: not normal: f may grow m
	_ = s
}

func ex4(a []int, i int, b bool) {
	_ = a[i] > 0 && f() > 0       // 54: normal: the left operand is evaluated first
	_ = f() > 0 || a[i] > 0       // 55: normal: the right operand after the left
	_ = b && (a[i] > 0) == (f() > 0) // 56: not normal: a[i] and f() are both on the right
}
`
	got := nonNormal(t, src)
	want := []int{11, 13, 14, 16, 18, 19, 31, 32, 33, 34, 44, 45, 47, 48, 49, 56}
	if len(got) != len(want) {
		t.Fatalf("got %v, want %v", got, want)
	}
	for i := range got {
		if got[i] != want[i] {
			t.Fatalf("got %v, want %v", got, want)
		}
	}
}

// A var spec is checked if goose translates one of its variables: each
// variable's initialization is translated on its own.
func TestSelectedSpec(t *testing.T) {
	src := `package p

var glob int

func f() int { return 0 }

var a, b = glob + f(), 1
`
	fset, f, info := check(t, src)
	onlyA := func(obj types.Object) bool { return obj.Name() == "a" }
	vs := CheckFile(info, f, onlyA)
	if len(vs) != 1 || fset.Position(vs[0].Pos).Line != 7 {
		t.Fatalf("got %v, want a violation at line 7", vs)
	}
}
