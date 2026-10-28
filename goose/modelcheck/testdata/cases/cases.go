// Package cases holds the statements modelcheck must report, each marked with
// a "want" comment, and statements it must not report.
package cases

import "unsafe"

type meta struct{ a, b, c, d, e, f, g, h uint64 }

type withArray struct {
	H uint64
	A [8]uint64
}

type tagged struct {
	a uint64 `json:"a"`
	b uint64 `json:"b"`
}

type untagged struct{ a, b uint64 }

type small struct{ x uint32 }

// Pointer-free but not plain: reported all the same.
type padded struct {
	a uint8
	b uint64
}
type blank struct {
	a uint32
	_ uint32
}
type floats struct{ x float64 }
type bools struct{ b bool }
type empty struct{}

// Not pointer-free: never reported.
type ptrs struct{ p, q *int }
type strs struct{ s string }

type pair[T any] struct{ x, y T }

type twoPointers struct{ x, y *meta }
type twoSlices struct{ a, b []meta }

type inner struct{ A, B meta }
type embedsTwo struct {
	*inner
	other *inner
}
type node struct {
	next *node
	A, B meta
}

var global meta
var globalArr [4]meta

func copies(p, q *meta, wp, wq *withArray, s, t []meta, arr *[4]meta, buf []uint64) {
	*p = *q                                                               // want
	wp.A = wq.A                                                           // want
	s[0] = t[1]                                                           // want
	s[0], t[1] = t[1], s[0]                                               // want
	arr[1] = *p                                                           // want
	(*p) = (*q)                                                           // want
	*p = meta(*q)                                                         // want
	globalArr[0] = s[2]                                                   // want
	s[1:][0] = s[0]                                                       // want
	s[next()] = s[0]                                                      // want
	*(*meta)(unsafe.Pointer(&buf[1])) = *(*meta)(unsafe.Pointer(&buf[0])) // want
	*(*[8]uint64)(buf[1:9]) = *(*[8]uint64)(buf[0:8])                     // want
	*(*[8]uint64)(buf[1:9]) = [8]uint64(buf[0:8])                         // want
	(*withArray)(unsafe.Pointer(&buf[1])).A = [8]uint64(buf)              // want
	var x [2]untagged
	x[0] = untagged(*(*tagged)(unsafe.Pointer(&buf[0]))) // want
	for _, s[0] = range t {                              // want
	}
	*(*small)(unsafe.Pointer(&buf[0])) = *(*small)(unsafe.Pointer(&buf[1])) // want
}

// Copies through two loaded pointers or slices with one root (the review of
// draft 8): gc gives the chunked result on overlapping views.
func loadedBases(pr *twoPointers, ts *twoSlices, xs [][]meta, e *embedsTwo) {
	*pr.y = *pr.x       // want
	ts.b[0] = ts.a[0]   // want
	xs[1][0] = xs[0][0] // want
	e.A = e.other.B     // want
	e.B = e.A           // want
}

func pointerFreeNotPlain(pa, pb *padded, ba, bb *blank, fa, fb *floats, oa, ob *bools, ea, eb *empty) {
	*pa = *pb // want
	*ba = *bb // want
	*fa = *fb // want
	*oa = *ob // want
	*ea = *eb // want
}

// Arrays with pointers are reported: in safe Go, overlapping slices converted
// to a named and an unnamed array pointer are copied with a Move (the review
// of draft 9): gc gives 0 0 0 0 0 0 0 0 0 9 for strings 0 to 9. Structs with
// pointers are not: no view of one can partially overlap another.
type strArr [8]string

func withPointers(rp, rq *ptrs, sp, sq *strs, s []string, ap, aq *[2]*int) {
	*rp = *rq
	*sp = *sq
	*ap = *aq // want
	p := (*strArr)(s[1:9])
	q := (*[8]string)(s[0:8])
	*p = *q // want
}

// A base with a composite literal is never the same base: types.ExprString
// abbreviates literals (the review of draft 9).
type holder struct{ A meta }

func literalBases(p, q *holder) {
	[]*holder{p, q}[0].A = []*holder{q, p}[0].A // want
}

// Package-variable literals are built in place (the review of draft 9).
type withTwo struct {
	H uint64
	A [8]uint64
}

func get() *[8]uint64 { return new([8]uint64) }

var built = withTwo{A: *get()}             // want
var nested = [1]withTwo{{H: 1, A: *get()}} // want

var arrVar [8]uint64
var notBuilt = withTwo{H: 1, A: arrVar}
var notBuilt2 = withTwo{A: [8]uint64{1, 2}}

// A call gc may inline and build in place (the third review): mk's
// `return withTwo{A: *p}` becomes built.A = *P in the variable.
func mk(p *[8]uint64) withTwo { return withTwo{A: *p} }

var P *[8]uint64
var inlined = mk(P)                   // want
var inlinedNested = [1]withTwo{mk(P)} // want
var pointerResult = &withTwo{H: 1}    // a fresh object
var scalarResult = next()             // nothing to move
var pointerCall = func() *withTwo { return nil }()

func next() int { return 0 }

var freshElem = withTwo{A: *new([8]uint64)}

// A base allocated by the place itself (new, make, a literal) is a fresh
// object, which no other side can view.
func freshBases[T any](p *meta, s []meta, d *T, xs []T, n int) {
	*p = *new(meta)
	s[0] = *new(meta)
	*d = *new(T)
	xs[0] = *new(T)
	(&node{}).A = *p
	*p = new([4]meta)[1]
	[]meta{*p}[0] = s[1]
	*p = make([]meta, n)[0]
	for _, (&node{}).A = range s {
	}
	// A pointer loaded from a fresh object is not fresh.
	*[]*meta{p}[0] = s[0] // want
	*new(*meta) = p
	**new(*meta) = s[0] // want
}

func generic[T any](d, s *T, xs, ys []T, ps []pair[T]) {
	*d = *s       // want
	xs[0] = ys[1] // want
	ps[0].x = *s  // want
	// The same base.
	xs[0], xs[1] = xs[1], xs[0]
	ps[0] = ps[1]
	ps[0].x = ps[1].y
}

func sameBase(p *meta, s []meta, wp *withArray, arr *[4]meta, i, j int, n *node, ys [][4]meta, e *embedsTwo) {
	s[i], s[j] = s[j], s[i]
	s[i+1] = s[len(s)-1]
	*p = *p
	arr[0] = arr[3]
	(*arr)[1] = arr[2]
	var local [4]meta
	local[1] = local[2]
	*(*meta)(unsafe.Pointer(&wp.A)) = *(*meta)(unsafe.Pointer(&wp.A))
	n.A = n.B
	n.next.A = n.next.B
	ys[i][0] = ys[j][1]
	e.other.A = e.other.B
}

func notReported(p, q *meta, s []meta, m map[int]meta, f func() meta, rp, rq *ptrs, sp, sq *strs) {
	// A whole variable on either side.
	x := *p
	*p = x
	x = *q
	global = *p
	*p = global
	var y meta = *q
	_ = y
	// The right side is not read from memory.
	*p = f()
	*p = meta{a: q.a}
	*p = m[0]
	m[1] = *p
	// Integer copies are one load and one store.
	*(*uint64)(unsafe.Pointer(&p.b)) = *(*uint64)(unsafe.Pointer(&p.a))
	// A range into a whole variable.
	for _, x = range s {
	}
	_ = x
}
