// Package diff runs the S0 reflect model (reflectmodel, written by ../gen.sh from
// goose/model/overlay/reflect over the harness reflectcore) against the real reflect: on a value
// corpus, TypeOf, ValueOf, Indirect, Value.{Kind, Type, IsValid, IsNil, Elem, Interface,
// CanInterface, CanAddr, CanSet}, Type.{Kind, Elem} and Kind.String agree, results and panic
// values. A model panic of a *ValueError matches Go's by Method and Kind (Method only where the
// model names it: valueMethodName's is arbitrary in the model, D.1), any other panic by its
// string. The model stuck where Go returns fails the test; the model stuck where Go panics is
// allowed and logged.
package diff

import (
	"errors"
	"fmt"
	"reflect"
	"sort"
	"strings"
	"testing"
	"unsafe"

	"github.com/mit-pdos/perennial/goose/model/reflect/harness/reflectcore"
	rm "github.com/mit-pdos/perennial/goose/model/reflect/harness/reflectmodel"
)

// An outcome: a result in a form both sides share, or a panic.
type outcome struct {
	val      any
	panicked bool
	stuck    bool
	pv       string // the panic, canonical
	method   string // a ValueError's Method
	vErr     bool
	vKind    uint
}

func run(f func() any) (o outcome) {
	defer func() {
		if o.panicked {
			p := recover()
			switch e := p.(type) {
			case *reflect.ValueError:
				o.vErr, o.method, o.vKind, o.pv = true, e.Method, uint(e.Kind), e.Error()
			case *rm.ValueError:
				o.vErr, o.method, o.vKind, o.pv = true, e.Method, uint(e.Kind), e.Error()
			case string:
				o.stuck = reflectcore.IsStuck(p)
				o.pv = e
			case error:
				o.pv = e.Error()
			default:
				o.pv = fmt.Sprint(p)
			}
		}
	}()
	o.panicked = true
	o.val = f()
	o.panicked = false
	return o
}

// realTypeOf is the type a model Type stands for: the T of its token any((*T)(nil)).
func realTypeOf(t rm.Type) reflect.Type {
	if t == nil {
		return nil
	}
	return reflect.ValueOf(t).Field(0).Elem().Type().Elem()
}

// vsum is a Value's observable summary, for comparing Values of the two sides.
type vsum struct {
	valid                 bool
	kind                  uint
	typ                   reflect.Type
	canAddr, canSet, canI bool
}

func sumReal(v reflect.Value) vsum {
	if !v.IsValid() {
		return vsum{}
	}
	return vsum{true, uint(v.Kind()), v.Type(), v.CanAddr(), v.CanSet(), v.CanInterface()}
}

func sumModel(v rm.Value) vsum {
	if !v.IsValid() {
		return vsum{}
	}
	return vsum{true, uint(v.Kind()), realTypeOf(v.Type()), v.CanAddr(), v.CanSet(), v.CanInterface()}
}

// same compares results: anys by dynamic type and deep equality (funcs by code pointer).
func same(a, b any) bool {
	if a == nil || b == nil {
		return a == nil && b == nil
	}
	if reflect.TypeOf(a) != reflect.TypeOf(b) {
		return false
	}
	va, vb := reflect.ValueOf(a), reflect.ValueOf(b)
	if va.Kind() == reflect.Func {
		return va.IsNil() == vb.IsNil() && va.Pointer() == vb.Pointer()
	}
	return reflect.DeepEqual(a, b)
}

// report collects the outcomes of the whole run.
type report struct {
	t           *testing.T
	stuckOnOK   []string // failures: model stuck, Go returns
	stuckOnPanc []string // allowed: model stuck, Go panics
	arbMethod   map[string]bool
	n           int
}

func (r *report) cmp(name string, goO, mO outcome) bool {
	r.t.Helper()
	r.n++
	switch {
	case mO.stuck && !goO.panicked:
		r.stuckOnOK = append(r.stuckOnOK, name)
		r.t.Errorf("%s: model stuck (%s), Go returns %#v", name, mO.pv, goO.val)
		return false
	case mO.stuck:
		r.stuckOnPanc = append(r.stuckOnPanc, name+" (Go: "+goO.pv+")")
		return false
	case goO.panicked != mO.panicked:
		r.t.Errorf("%s: Go %s, model %s", name, desc(goO), desc(mO))
		return false
	case goO.panicked:
		if goO.vErr != mO.vErr || goO.vKind != mO.vKind {
			r.t.Errorf("%s: Go panics %s, model %s", name, desc(goO), desc(mO))
		} else if goO.vErr && goO.method != mO.method {
			if mO.method == "unknown method" || strings.Contains(mO.method, "reflectmodel.") {
				r.arbMethod[name+": Go "+goO.method+", model "+mO.method] = true
			} else {
				r.t.Errorf("%s: Go ValueError.Method %q, model %q", name, goO.method, mO.method)
			}
		} else if !goO.vErr && goO.pv != mO.pv {
			r.t.Errorf("%s: Go panics %q, model %q", name, goO.pv, mO.pv)
		}
		return false
	case !same(goO.val, mO.val):
		r.t.Errorf("%s: Go %#v, model %#v", name, goO.val, mO.val)
		return false
	}
	return true
}

func desc(o outcome) string {
	if !o.panicked {
		return fmt.Sprintf("returns %#v", o.val)
	}
	if o.vErr {
		return fmt.Sprintf("panics ValueError{%q, %d} (%s)", o.method, o.vKind, o.pv)
	}
	return fmt.Sprintf("panics %q", o.pv)
}

// checkValue compares every S0 operation on a pair of Values meant to be the same, and recurses
// into Elem and Indirect.
func (r *report) checkValue(name string, gv func() reflect.Value, mv func() rm.Value, depth int) {
	gV, mV := run(func() any { return gv() }), run(func() any { return mv() })
	if gV.panicked || mV.panicked {
		r.cmp(name, gV, mV)
		return
	}
	g, m := gV.val.(reflect.Value), mV.val.(rm.Value)
	r.cmp(name+".Kind", run(func() any { return uint(g.Kind()) }), run(func() any { return uint(m.Kind()) }))
	r.cmp(name+".Kind.String", run(func() any { return g.Kind().String() }), run(func() any { return m.Kind().String() }))
	r.cmp(name+".IsValid", run(func() any { return g.IsValid() }), run(func() any { return m.IsValid() }))
	r.cmp(name+".IsNil", run(func() any { return g.IsNil() }), run(func() any { return m.IsNil() }))
	r.cmp(name+".CanAddr", run(func() any { return g.CanAddr() }), run(func() any { return m.CanAddr() }))
	r.cmp(name+".CanSet", run(func() any { return g.CanSet() }), run(func() any { return m.CanSet() }))
	r.cmp(name+".CanInterface", run(func() any { return g.CanInterface() }), run(func() any { return m.CanInterface() }))
	r.cmp(name+".Interface", run(func() any { return g.Interface() }), run(func() any { return m.Interface() }))
	r.cmp(name+".Type", run(func() any { return g.Type() }), run(func() any { return realTypeOf(m.Type()) }))
	if r.cmp(name+".Type.Kind", run(func() any { return uint(g.Type().Kind()) }), run(func() any { return uint(m.Type().Kind()) })) {
		r.cmp(name+".Type.Elem", run(func() any { return g.Type().Elem() }), run(func() any { return realTypeOf(m.Type().Elem()) }))
	}
	if depth == 0 {
		return
	}
	r.cmpValue(name+".Elem", run(func() any { return sumReal(g.Elem()) }), run(func() any { return sumModel(m.Elem()) }),
		func() reflect.Value { return g.Elem() }, func() rm.Value { return m.Elem() }, depth)
	r.cmpValue(name+".Indirect", run(func() any { return sumReal(reflect.Indirect(g)) }), run(func() any { return sumModel(rm.Indirect(m)) }),
		func() reflect.Value { return reflect.Indirect(g) }, func() rm.Value { return rm.Indirect(m) }, depth)
}

func (r *report) cmpValue(name string, gO, mO outcome, gv func() reflect.Value, mv func() rm.Value, depth int) {
	if r.cmp(name, gO, mO) && gO.val.(vsum).valid {
		r.checkValue(name, gv, mv, depth-1)
	}
}

func (r *report) finish() {
	r.t.Logf("%d comparisons", r.n)
	// grouped by the last operation and Go's panic without the type
	groups := map[string]int{}
	for _, s := range r.stuckOnPanc {
		name, goPanic, _ := strings.Cut(s, " (Go: ")
		op := name
		if strings.HasPrefix(name, "TypeOf(") {
			op = "TypeOf(x)" + name[strings.LastIndex(name, ")")+1:]
		} else if segs := strings.Split(name, "."); len(segs) > 2 {
			op = "Value." + strings.Join(segs[len(segs)-2:], ".")
		}
		if i := strings.Index(goPanic, " type "); i >= 0 {
			goPanic = goPanic[:i+5] + " T"
		}
		groups[op+" / Go: "+strings.TrimSuffix(goPanic, ")")]++
	}
	var gs []string
	for g, n := range groups {
		gs = append(gs, fmt.Sprintf("%s (%d cases)", g, n))
	}
	sort.Strings(gs)
	for _, g := range gs {
		r.t.Logf("model stuck where Go panics (allowed): %s", g)
	}
	var ms []string
	for m := range r.arbMethod {
		ms = append(ms, m)
	}
	sort.Strings(ms)
	for _, m := range ms {
		r.t.Logf("ValueError.Method from valueMethodName (arbitrary in the model): %s", m)
	}
}

func newReport(t *testing.T) *report { return &report{t: t, arbMethod: map[string]bool{}} }

// The value corpus.

type myInt int
type myString string
type myPtr *int
type mySlice []int
type myMap map[string]int
type myFunc func() int
type myChan chan int
type myUnsafe unsafe.Pointer
type myArr [2]string
type myIface interface{ M() }
type impl struct{ n int }

func (impl) M() {}

type S struct {
	A int
	b string
	_ int
	*S
}
type onePtr struct{ p *int }
type oneArr [1]*int
type nested struct{ x oneArr }
type G[T any] struct{ V T }
type GP[T any] *T

func f0() int { return 0 }

// A corpus entry: x as any, and the pointer &v to a variable v := x of x's static type.
type entry struct {
	name string
	x    any
	p    any
}

func e[T any](name string, x T) entry {
	v := x
	return entry{name, x, &v}
}

func values() []entry {
	n := 3
	ch := make(chan int, 1)
	var ni myIface
	return []entry{
		e("bool", true), e("int", -1), e("int8", int8(2)), e("int16", int16(3)), e("int32", int32(4)),
		e("int64", int64(5)), e("uint", uint(6)), e("uint8", uint8(7)), e("uint16", uint16(8)),
		e("uint32", uint32(9)), e("uint64", uint64(10)), e("uintptr", uintptr(11)),
		e("float32", float32(1.5)), e("float64", 2.5), e("complex64", complex64(1i)),
		e("complex128", 2+3i), e("string", "s"), e("empty string", ""),
		e("[0]int", [0]int{}), e("[1]string", [1]string{"a"}), e("[3]int", [3]int{1, 2, 3}),
		e("oneArr", oneArr{&n}), e("[1]*int nil", [1]*int{}), e("myArr", myArr{"x", "y"}),
		e("chan", ch), e("nil chan", (chan int)(nil)), e("<-chan", (<-chan int)(ch)),
		e("chan<-", (chan<- int)(ch)), e("myChan", myChan(ch)), e("nil myChan", myChan(nil)),
		e("func", f0), e("nil func", (func())(nil)), e("myFunc", myFunc(f0)), e("nil myFunc", myFunc(nil)),
		e("map", map[string]int{"a": 1}), e("empty map", map[int]bool{}),
		e("nil map", (map[string]int)(nil)), e("myMap", myMap{"b": 2}), e("nil myMap", myMap(nil)),
		e("*int", &n), e("nil *int", (*int)(nil)), e("**int", func() **int { p := &n; return &p }()),
		e("nil **int", (**int)(nil)), e("myPtr", myPtr(&n)), e("nil myPtr", myPtr(nil)),
		e("*S", &S{A: 1}), e("nil *S", (*S)(nil)), e("GP[int]", GP[int](&n)), e("nil GP", GP[string](nil)),
		e("slice", []int{1}), e("empty slice", []int{}), e("make slice", make([]int, 0)),
		e("nil slice", []int(nil)), e("mySlice", mySlice{2}), e("nil mySlice", mySlice(nil)),
		e("[]byte", []byte("b")),
		e("struct{}", struct{}{}), e("S", S{A: 1, b: "b"}), e("onePtr", onePtr{&n}),
		e("onePtr nil", onePtr{}), e("nested", nested{oneArr{&n}}), e("impl", impl{1}),
		e("G[int]", G[int]{1}), e("G[*int]", G[*int]{&n}), e("struct{p *int}", struct{ p *int }{&n}),
		e("unsafe.Pointer", unsafe.Pointer(&n)), e("nil unsafe.Pointer", unsafe.Pointer(nil)),
		e("myUnsafe", myUnsafe(&n)), e("nil myUnsafe", myUnsafe(nil)),
		e("myInt", myInt(4)), e("myString", myString("t")),
		// interface-typed variables: p is a pointer to an interface
		e[any]("any(int)", 5), e[any]("any(nil)", nil), e[any]("any(*int nil)", (*int)(nil)),
		e[error]("error(nil)", nil), e[error]("error", errors.New("e")),
		e[myIface]("myIface", impl{2}), e[myIface]("myIface(*impl)", &impl{3}),
		e[myIface]("myIface nil", ni), e[any]("any(any(slice))", []any{nil}),
		e[any]("any(*any)", func() *any { var a any = 1; return &a }()),
	}
}

// Every S0 operation agrees on ValueOf(x), on ValueOf(&x) and on ValueOf(&x).Elem() (an
// addressable value; for an interface-typed x, an Interface-kind value), recursively through
// Elem and Indirect; TypeOf agrees with its Kind and Elem.
func TestDifferentialValues(t *testing.T) {
	r := newReport(t)
	r.checkValue("ValueOf(nil)", func() reflect.Value { return reflect.ValueOf(nil) }, func() rm.Value { return rm.ValueOf(nil) }, 2)
	for _, c := range values() {
		x, p := c.x, c.p
		r.checkValue("ValueOf("+c.name+")", func() reflect.Value { return reflect.ValueOf(x) }, func() rm.Value { return rm.ValueOf(x) }, 2)
		r.checkValue("ValueOf(&"+c.name+")", func() reflect.Value { return reflect.ValueOf(p) }, func() rm.Value { return rm.ValueOf(p) }, 3)
		for _, y := range []any{x, p} {
			name := fmt.Sprintf("TypeOf(%T)", y)
			r.cmp(name, run(func() any { return reflect.TypeOf(y) }), run(func() any { return realTypeOf(rm.TypeOf(y)) }))
			if y == nil {
				continue
			}
			if r.cmp(name+".Kind", run(func() any { return uint(reflect.TypeOf(y).Kind()) }), run(func() any { return uint(rm.TypeOf(y).Kind()) })) {
				r.cmp(name+".Elem", run(func() any { return reflect.TypeOf(y).Elem() }), run(func() any { return realTypeOf(rm.TypeOf(y).Elem()) }))
			}
		}
	}
	if rm.TypeOf(nil) != nil || reflect.TypeOf(nil) != nil {
		t.Errorf("TypeOf(nil) is not the nil Type")
	}
	r.finish()
}

// Kind.String for every kind and beyond.
func TestKindString(t *testing.T) {
	for k := uint(0); k < 40; k++ {
		if g, m := reflect.Kind(k).String(), rm.Kind(k).String(); g != m {
			t.Errorf("Kind(%d).String(): Go %q, model %q", k, g, m)
		}
	}
	if g, m := reflect.Kind(1000).String(), rm.Kind(1000).String(); g != m {
		t.Errorf("Kind(1000).String(): Go %q, model %q", g, m)
	}
	if rm.Ptr != rm.Pointer || uint(rm.UnsafePointer) != uint(reflect.UnsafePointer) {
		t.Errorf("Kind constants")
	}
}

// The specreq shapes.

// etcd's txn.isNil: msg == nil || reflect.ValueOf(msg).IsNil().
func isNilReal(msg myIface) bool { return msg == nil || reflect.ValueOf(msg).IsNil() }
func isNilModel(msg myIface) bool { return msg == nil || rm.ValueOf(msg).IsNil() }

// apimachinery's conversion.EnforcePtr, with the error naming the Kind instead of the Type
// (Type.String is not in S0).
func enforcePtrReal(obj any) (reflect.Value, error) {
	v := reflect.ValueOf(obj)
	if v.Kind() != reflect.Pointer {
		if v.Kind() == reflect.Invalid {
			return reflect.Value{}, fmt.Errorf("expected pointer, but got invalid kind")
		}
		return reflect.Value{}, fmt.Errorf("expected pointer, but got %v kind", v.Kind())
	}
	if v.IsNil() {
		return reflect.Value{}, fmt.Errorf("expected pointer, but got nil")
	}
	return v.Elem(), nil
}

func enforcePtrModel(obj any) (rm.Value, error) {
	v := rm.ValueOf(obj)
	if v.Kind() != rm.Pointer {
		if v.Kind() == rm.Invalid {
			return rm.Value{}, fmt.Errorf("expected pointer, but got invalid kind")
		}
		return rm.Value{}, fmt.Errorf("expected pointer, but got %v kind", v.Kind())
	}
	if v.IsNil() {
		return rm.Value{}, fmt.Errorf("expected pointer, but got nil")
	}
	return v.Elem(), nil
}

func TestSpecreqShapes(t *testing.T) {
	r := newReport(t)
	var nilImpl *impl
	for _, c := range []struct {
		name string
		msg  myIface
	}{{"nil", nil}, {"typed nil", nilImpl}, {"non-nil pointer", &impl{}}, {"value", impl{}}} {
		msg := c.msg
		r.cmp("isNil("+c.name+")", run(func() any { return isNilReal(msg) }), run(func() any { return isNilModel(msg) }))
	}
	// MustPanicIsNilZeroValue, MustPanicIsNilStruct
	g, m := run(func() any { return reflect.ValueOf(nil).IsNil() }), run(func() any { return rm.ValueOf(nil).IsNil() })
	r.cmp("ValueOf(nil).IsNil", g, m)
	if m.pv != "reflect: call of reflect.Value.IsNil on zero Value" || m.method != "reflect.Value.IsNil" || m.vKind != 0 {
		t.Errorf("ValueOf(nil).IsNil: model panics %s", desc(m))
	}
	g, m = run(func() any { return reflect.ValueOf(struct{}{}).IsNil() }), run(func() any { return rm.ValueOf(struct{}{}).IsNil() })
	r.cmp("ValueOf(struct{}{}).IsNil", g, m)
	if m.pv != "reflect: call of reflect.Value.IsNil on struct Value" || m.vKind != uint(reflect.Struct) {
		t.Errorf("ValueOf(struct{}{}).IsNil: model panics %s", desc(m))
	}
	n := 1
	for _, c := range values() {
		for _, obj := range []any{c.x, c.p, nil, (*int)(nil), &n} {
			gO := run(func() any { v, err := enforcePtrReal(obj); return fmt.Sprint(sumReal(v), err) })
			mO := run(func() any { v, err := enforcePtrModel(obj); return fmt.Sprint(sumModel(v), err) })
			r.cmp(fmt.Sprintf("EnforcePtr(%T)", obj), gO, mO)
		}
	}
	// ReqTypedNil's typedNilString half: a typed nil pointer in an interface is not nil, its Value is.
	var p *impl
	var i myIface = p
	if i == nil || !isNilModel(i) || rm.ValueOf(i).Kind() != rm.Pointer {
		t.Errorf("typed nil: model")
	}
	r.finish()
}
