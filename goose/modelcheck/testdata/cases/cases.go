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

// Not plain: padded, a blank field, a pointer, a float, a bool, zero size.
type padded struct {
	a uint8
	b uint64
}
type trailing struct {
	a uint64
	b uint32
}
type blank struct {
	a uint32
	_ uint32
}
type ptrs struct{ p, q *int }
type floats struct{ x float64 }
type bools struct{ b bool }
type empty struct{}

type pair[T any] struct{ x, y T }

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

func next() int { return 0 }

func generic[T any](d, s *T, xs, ys []T, ps []pair[T]) {
	*d = *s       // want
	xs[0] = ys[1] // want
	ps[0].x = *s  // want
	// The same root.
	xs[0], xs[1] = xs[1], xs[0]
	ps[0] = ps[1]
	ps[0].x = ps[1].y
}

func sameRoot[M ~map[int]meta](p *meta, s []meta, wp *withArray, arr *[4]meta, i, j int, m M) {
	s[i], s[j] = s[j], s[i]
	s[i+1] = s[len(s)-1]
	*p = *p
	arr[0] = arr[3]
	(*arr)[1] = arr[2]
	var local [4]meta
	local[1] = local[2]
	q := (*meta)(unsafe.Pointer(&wp.A))
	*(*meta)(unsafe.Pointer(&wp.A)) = *(*meta)(unsafe.Pointer(&wp.A))
	_ = q
}

func notReported(p, q *meta, s []meta, m map[int]meta, f func() meta) {
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
	// Not plain.
	var pa, pb padded
	pp, pq := &pa, &pb
	*pp = *pq
	var ta, tb trailing
	tp, tq := &ta, &tb
	*tp = *tq
	var ba, bb blank
	bp, bq := &ba, &bb
	*bp = *bq
	var ra, rb ptrs
	rp, rq := &ra, &rb
	*rp = *rq
	var fa, fb floats
	fp, fq := &fa, &fb
	*fp = *fq
	var oa, ob bools
	op, oq := &oa, &ob
	*op = *oq
	var ea, eb empty
	epp, epq := &ea, &eb
	*epp = *epq
	// A range into a whole variable.
	for _, x = range s {
	}
	_ = x
}
