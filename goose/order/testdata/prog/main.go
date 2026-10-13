// A program whose results depend on the evaluation order of its statements.
// Built with perennial-order, every check must hold: a statement's operands
// are evaluated strictly left to right, each completely before the next.
package main

import (
	"fmt"
	"os"
	"runtime/debug"
	"strings"

	"github.com/mit-pdos/perennial/goose/order/testdata/prog/gcorder"
)

var failed bool

func check(name string, got, want any) {
	if fmt.Sprint(got) != fmt.Sprint(want) {
		fmt.Printf("FAIL %s: got %v, want %v\n", name, got, want)
		failed = true
	}
}

var g = 1

func setg(v int) int { g = v; return 0 }

var log []string

func tr(s string, v int) int { log = append(log, s); return v }

type B bool

func bt(s string, v bool) B { log = append(log, s); return B(v) }

// package-level initializer: g0 is read before setg0 runs.
var pkgInit = g0 + setg0()
var g0 = 1

func setg0() int { g0 = 10; return 0 }

type ctr struct{ n int }

func (c *ctr) get(int) int { return c.n }
func (c ctr) val(int) int  { return c.n }

type getter interface{ get(int) int }

var cs = []ctr{{1}, {2}}

type box struct{ arr [2]int }

type outer struct{ box }
type outerP struct{ *box }

func main() {
	check("pkg var", pkgInit, 1)

	// reads before the calls to their right
	g = 1
	check("global + call", g+setg(100), 1)
	m := map[int]int{0: 1}
	check("map read + call", m[0]+func() int { m[0] = 7; return 0 }(), 1)
	a := []int{1, 2, 3}
	i := 0
	f := func() int { i = 2; return 0 }
	check("index read + call", a[i]+f(), 1)
	g = 1
	check("call + global", setg(100)+g, 100)

	// locality: each operand is evaluated completely before the next
	g = 1
	check("spec example", fmt.Sprint([]int{g, setg(2) + g}), "[1 2]")
	g = 1
	pair := func(x, y int) int { return 10*x + y }
	check("nested", pair(g, pair(setg(3), g)), 13)
	log = nil
	a = []int{0, 0}
	check("operand before call", pair(a[tr("i", 0)], func() int { a[0] = 9; log = append(log, "set"); return 0 }()), 0)
	check("operand order", strings.Join(log, ","), "i,set")

	// operands used as addresses, receivers
	bp, bp2 := &box{}, &box{arr: [2]int{5, 5}}
	cur := bp
	check("array through pointer", cur.arr[func() int { cur = bp2; return 0 }()], 0)
	cp := &cs[0]
	check("pointer receiver", cp.get(func() int { cp = &cs[1]; return 0 }()), 1)
	cp = &cs[0]
	check("value receiver through pointer", cp.val(func() int { cp.n = 7; return 0 }()), 1)
	cs[0].n = 1
	var gi getter = &cs[0]
	check("interface receiver", gi.get(func() int { gi = &cs[1]; return 0 }()), 1)
	mm := map[int]int{0: 1}
	mm[0] += func() int { mm[0] = 10; return 1 }()
	check("op= map element", mm[0], 2)
	ob := &outer{}
	var okb bool
	ob.arr[1], okb = 4, func() bool { return true }()
	_ = okb
	check("promoted array element", ob.arr[1], 4)
	op := &outerP{&box{}}
	op.arr[func() int { return 1 }()] = 5
	check("promoted array through a pointer", op.arr[1], 5)
	var key any = 1
	ml := map[any]int{key: 1, 2: func() int { key = 3; return 2 }()}
	_, has1 := ml[1]
	check("map literal key", has1, true)

	// calls in order, and op=
	log = nil
	a = []int{0, 0}
	a[tr("lhs", 0)] = tr("rhs", 5)
	check("call order", strings.Join(log, ","), "lhs,rhs")
	a = []int{0, 0}
	b := []int{0, 0}
	a[0] += func() int { a = b; return 3 }()
	check("op= target before rhs", fmt.Sprint(a, b), "[0 0] [0 0]")
	g = 1
	g += setg(5)
	check("op= read before rhs", g, 1)

	// short circuit keeps laziness
	log = nil
	ok := false
	_ = g > 0 && ok && bt("never", true) == true
	_ = g > 100 || bt("evaluated", true) == true
	check("short circuit", strings.Join(log, ","), "evaluated")
	var nb B = g > 0 && bt("named", true)
	check("named bool", nb, true)

	// if / else if
	log = nil
	g = 5
	if g == 1 && bt("if1", true) == true {
		log = append(log, "then1")
	} else if g+setg(6) == 6 && bt("if2", true) == true {
		log = append(log, "then2")
	}
	check("else if", strings.Join(log, ","), "")

	// for condition with calls
	n := 0
	g = 0
	for g+setg(g+1) < 3 {
		n++
	}
	check("for cond", n, 3)

	// switch: tagless, split at a case not in normal form
	g = 1
	log = nil
	switch {
	case bt("c1", false) == true:
		log = append(log, "b1")
	case g+setg(2) == 2:
		log = append(log, "b2")
	default:
		log = append(log, "def")
	}
	check("switch split", strings.Join(log, ","), "c1,def")

	// tagged switch with default first and a multi-expression clause
	g = 1
	log = nil
	switch tr("tag", 3) {
	default:
		log = append(log, "def")
	case 1:
		log = append(log, "one")
	case g + setg(1), g + setg(3):
		log = append(log, "match")
	}
	check("tagged multi", strings.Join(log, ","), "tag,def")

	// break inside a split switch leaves the whole switch
	g = 1
	log = nil
	switch {
	case g+setg(1) == 1:
		log = append(log, "x")
		break
	}
	check("switch break", strings.Join(log, ","), "x")

	// labels: break and continue through a rewritten loop header
	g = 0
	count := 0
outer:
	for _, v := range []int{g + setg(1), 2, 3} {
		for j := 0; j < 3; j++ {
			if j == 1 {
				continue outer
			}
			if v == 3 {
				break outer
			}
			count++
		}
	}
	check("labels", count, 2)

	// goto to a labeled statement that is rewritten
	g = 0
	tries := 0
again:
	if g+setg(g+1) < 2 {
		tries++
		goto again
	}
	check("goto", tries, 2) // g is read before setg runs

	// select operands in source order
	log = nil
	ch := make(chan int, 1)
	select {
	case ch <- tr("v1", 1) + g:
	case <-func() chan int { log = append(log, "c2"); return nil }():
	}
	check("select", strings.Join(log, ","), "v1,c2")

	// defer and go evaluate their arguments now
	g = 1
	done := make(chan int)
	go func(v int) { done <- v }(g + setg(9))
	check("go args", <-done, 1)
	func() {
		g = 1
		defer func(v int) { check("defer args", v, 1) }(g + setg(4))
	}()

	// grouped var, comma-ok receive, multi-value
	g = 1
	var (
		v1 = g + setg(2)
		v2 = g + setg(3)
	)
	check("grouped var", fmt.Sprint(v1, v2), "1 2")
	ch = make(chan int, 1)
	ch <- 5
	arr := []int{0, 0}
	var okr bool
	arr[g-3], okr = <-ch
	check("comma-ok recv", fmt.Sprint(arr, okr), "[5 0] true")
	two := func() (int, int) { g = 50; return 1, 2 }
	x1, x2 := g+0, 0
	x1, x2 = two()
	check("multi-value", fmt.Sprint(x1, x2, g), "1 2 50")

	// a panic in rewritten code is reported at its original line
	func() {
		defer func() {
			recover()
			check("panic line", strings.Contains(string(debug.Stack()), fmt.Sprintf("main.go:%d", panicLine)), true)
		}()
		var z []int
		_ = z[g] + setg(0) // panicLine
	}()

	// a package that is not translated keeps the compiler's order
	po, _ := gcorder.Parse()
	check("untranslated package", po.V, 1)

	if failed {
		os.Exit(1)
	}
	fmt.Println("ok")
}

const panicLine = 256
