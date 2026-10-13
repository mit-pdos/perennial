// A program whose results depend on the evaluation order of its statements.
// Built with perennial-order, every check must hold: events (calls, receives)
// run first, left to right, then the rest of the statement is evaluated.
package main

import (
	"fmt"
	"os"
	"runtime/debug"
	"strings"
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

// package-level initializer: g0 is read after setg runs.
var pkgInit = g0 + setg0()
var g0 = 1

func setg0() int { g0 = 10; return 0 }

func main() {
	check("pkg var", pkgInit, 10)

	// reads after the calls
	g = 1
	check("global + call", g+setg(100), 100)
	m := map[int]int{0: 1}
	check("map read + call", m[0]+func() int { m[0] = 7; return 0 }(), 7)
	a := []int{1, 2, 3}
	i := 0
	f := func() int { i = 2; return 0 }
	check("index read + call", a[i]+f(), 3)

	// calls in order, and op=
	log = nil
	a = []int{0, 0}
	a[tr("lhs", 0)] = tr("rhs", 5)
	check("call order", strings.Join(log, ","), "lhs,rhs")
	a = []int{0, 0}
	b := []int{0, 0}
	a[0] += func() int { a = b; return 3 }()
	check("op= target after rhs", fmt.Sprint(a, b), "[3 0] [3 0]")

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
	check("else if", strings.Join(log, ","), "if2,then2")

	// for condition with calls
	n := 0
	g = 0
	for g+setg(g+1) < 3 {
		n++
	}
	check("for cond", n, 2)

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
	check("switch split", strings.Join(log, ","), "c1,b2")

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
	check("tagged multi", strings.Join(log, ","), "tag,match")

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
	check("goto", tries, 1) // setg runs before g is read

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
	check("go args", <-done, 9)
	func() {
		g = 1
		defer func(v int) { check("defer args", v, 4) }(g + setg(4))
	}()

	// grouped var, comma-ok receive, multi-value
	g = 1
	var (
		v1 = g + setg(2)
		v2 = g + setg(3)
	)
	check("grouped var", fmt.Sprint(v1, v2), "2 3")
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

	if failed {
		os.Exit(1)
	}
	fmt.Println("ok")
}

const panicLine = 197
