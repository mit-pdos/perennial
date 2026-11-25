package diff

// The reflectlite model (reflectlitemodel, written by ../gen.sh from
// goose/model/overlay/internal/reflectlite) against the real reflect (internal/reflectlite cannot
// be imported) on the value corpus: TypeOf, ValueOf, Value.{Kind, IsNil, IsValid, CanSet, Type,
// Elem, Set}, Type.{Kind, Elem}; against reflect's AssignableTo and Implements on a type corpus;
// and the real errors/wrap.go over the model (errorsmodel) against the real errors.As, which runs
// the real reflectlite. The model may be stuck where Go returns (it is less defined, logged), but
// never returns or panics differently.

import (
	"errors"
	"fmt"
	"reflect"
	"sort"
	"strings"
	"testing"
	"unsafe"

	em "github.com/mit-pdos/perennial/goose/model/reflect/harness/errorsmodel"
	rlm "github.com/mit-pdos/perennial/goose/model/reflect/harness/reflectlitemodel"
	rm "github.com/mit-pdos/perennial/goose/model/reflect/harness/reflectmodel"
)

// realTypeOfL is the type a model Type stands for.
func realTypeOfL(t rlm.Type) reflect.Type {
	if t == nil {
		return nil
	}
	return reflect.ValueOf(t).Field(0).Elem().Type().Elem()
}

// liteOf is the model's Type of the type of a token.
func liteOf(tok any) rlm.Type { return rlm.TypeOf(tok).Elem() }

func tk[T any]() any { return (*T)(nil) }

// stuckLog collects the model's stuck points where Go returns (allowed: the model is less
// defined) and checks every other outcome.
type stuckLog struct {
	t     *testing.T
	stuck map[string]int
	n     int
}

func newStuckLog(t *testing.T) *stuckLog { return &stuckLog{t: t, stuck: map[string]int{}} }

func (l *stuckLog) cmp(group, name string, goO, mO outcome) bool {
	l.t.Helper()
	l.n++
	switch {
	case mO.stuck:
		if testing.Verbose() && strings.HasPrefix(group, "As") {
			l.t.Logf("stuck: %s (Go: %s)", name, desc(goO))
		}
		if goO.panicked {
			l.stuck[group+" (Go panics)"]++
		} else {
			l.stuck[group+" (Go returns)"]++
		}
		return false
	case goO.panicked != mO.panicked:
		l.t.Errorf("%s: Go %s, model %s", name, desc(goO), desc(mO))
		return false
	case goO.panicked:
		if goO.vErr != mO.vErr || goO.vKind != mO.vKind || goO.pv != mO.pv && !goO.vErr ||
			goO.vErr && goO.method != mO.method {
			l.t.Errorf("%s: Go panics %s, model %s", name, desc(goO), desc(mO))
		}
		return false
	case !same(goO.val, mO.val):
		l.t.Errorf("%s: Go %#v, model %#v", name, goO.val, mO.val)
		return false
	}
	return true
}

func (l *stuckLog) finish() {
	l.t.Logf("%d comparisons", l.n)
	var gs []string
	for g, n := range l.stuck {
		gs = append(gs, fmt.Sprintf("%s: %d", g, n))
	}
	sort.Strings(gs)
	for _, g := range gs {
		l.t.Logf("model stuck: %s", g)
	}
}

func (l *stuckLog) checkLite(name string, gv func() reflect.Value, mv func() rlm.Value, depth int) {
	gV, mV := run(func() any { return gv() }), run(func() any { return mv() })
	if gV.panicked || mV.panicked {
		l.cmp("ValueOf", name, gV, mV)
		return
	}
	g, m := gV.val.(reflect.Value), mV.val.(rlm.Value)
	l.cmp("Kind", name+".Kind", run(func() any { return uint(g.Kind()) }), run(func() any { return uint(m.Kind()) }))
	l.cmp("IsValid", name+".IsValid", run(func() any { return g.IsValid() }), run(func() any { return m.IsValid() }))
	l.cmp("IsNil", name+".IsNil", run(func() any { return g.IsNil() }), run(func() any { return m.IsNil() }))
	l.cmp("CanSet", name+".CanSet", run(func() any { return g.CanSet() }), run(func() any { return m.CanSet() }))
	l.cmp("Type", name+".Type", run(func() any { return g.Type() }), run(func() any { return realTypeOfL(m.Type()) }))
	if l.cmp("Type.Kind", name+".Type.Kind", run(func() any { return uint(g.Type().Kind()) }), run(func() any { return uint(m.Type().Kind()) })) {
		l.cmp("Type.Elem", name+".Type.Elem", run(func() any { return g.Type().Elem() }), run(func() any { return realTypeOfL(m.Type().Elem()) }))
	}
	if depth == 0 {
		return
	}
	gE, mE := run(func() any { return g.Elem().IsValid() }), run(func() any { return m.Elem().IsValid() })
	if l.cmp("Elem", name+".Elem", gE, mE) && gE.val.(bool) {
		l.checkLite(name+".Elem", func() reflect.Value { return g.Elem() }, func() rlm.Value { return m.Elem() }, depth-1)
	}
}

// TypeOf, ValueOf and the Value methods agree on ValueOf(x), ValueOf(&x) and ValueOf(&x).Elem().
func TestReflectliteValues(t *testing.T) {
	l := newStuckLog(t)
	l.checkLite("ValueOf(nil)", func() reflect.Value { return reflect.ValueOf(nil) }, func() rlm.Value { return rlm.ValueOf(nil) }, 1)
	for _, en := range values() {
		x, p := en.x, en.p
		l.checkLite("ValueOf("+en.name+")", func() reflect.Value { return reflect.ValueOf(x) }, func() rlm.Value { return rlm.ValueOf(x) }, 2)
		l.checkLite("ValueOf(&"+en.name+")", func() reflect.Value { return reflect.ValueOf(p) }, func() rlm.Value { return rlm.ValueOf(p) }, 2)
		l.cmp("TypeOf", "TypeOf("+en.name+")", run(func() any { return reflect.TypeOf(x) }), run(func() any { return realTypeOfL(rlm.TypeOf(x)) }))
		l.cmp("TypeOf", "TypeOf(&"+en.name+")", run(func() any { return reflect.TypeOf(p) }), run(func() any { return realTypeOfL(rlm.TypeOf(p)) }))
	}
	l.finish()
	if n := l.stuck["Kind (Go returns)"] + l.stuck["IsNil (Go returns)"] + l.stuck["Type (Go returns)"] +
		l.stuck["Elem (Go returns)"] + l.stuck["ValueOf (Go returns)"] + l.stuck["TypeOf (Go returns)"]; n > 0 {
		t.Errorf("the model is stuck where Go returns on %d S0-level operations", n)
	}
}

// fresh is a pointer to a new variable holding *p.
func fresh(p any) any {
	v := reflect.New(reflect.TypeOf(p).Elem())
	v.Elem().Set(reflect.ValueOf(p).Elem())
	return v.Interface()
}

// ValueOf(&dst).Elem().Set(ValueOf(src)) for every pair of the corpus: the same panics and the
// same *dst after.
func TestReflectliteSet(t *testing.T) {
	l := newStuckLog(t)
	vs := values()
	for _, d := range vs {
		for _, s := range vs {
			name := "Set(" + d.name + ", " + s.name + ")"
			pg, pm := fresh(d.p), fresh(d.p)
			x := s.x
			gO := run(func() any { reflect.ValueOf(pg).Elem().Set(reflect.ValueOf(x)); return nil })
			mO := run(func() any { rlm.ValueOf(pm).Elem().Set(rlm.ValueOf(x)); return nil })
			// reflect names itself in its messages, reflectlite reflectlite
			mO.pv = strings.Replace(mO.pv, "reflectlite.Set", "reflect.Set", 1)
			if l.cmp("Set", name, gO, mO) {
				l.cmp("Set", name+" *dst", run(func() any { return reflect.ValueOf(pg).Elem().Interface() }),
					run(func() any { return reflect.ValueOf(pm).Elem().Interface() }))
			}
		}
		// the unaddressable ValueOf(x) and the zero Value as destinations
		pg := fresh(d.p)
		l.cmp("Set", "Set(ValueOf("+d.name+"))", run(func() any {
			reflect.ValueOf(reflect.ValueOf(pg).Elem().Interface()).Set(reflect.ValueOf(1))
			return nil
		}),
			run(func() any { rlm.ValueOf(reflect.ValueOf(pg).Elem().Interface()).Set(rlm.ValueOf(1)); return nil }))
	}
	l.finish()
}

// Error and assignability corpus types.

type E1 struct{ msg string }

func (e *E1) Error() string { return e.msg }

type E2 struct{}

func (E2) Error() string { return "e2" }

type E3 int

func (E3) Error() string { return "e3" }

type E3b int

func (E3b) Error() string { return "e3b" }

// SE has the underlying type of the unnamed struct{ E2 }, which implements error by promotion.
type SE struct{ E2 }

// tagSE has the underlying type of the unnamed struct{ E2 `json:"t"` }, a tag that goose's translation
// of a defined struct type drops: Go assigns a tagSE to that unnamed type, so the model must not
// decide (from the underlying types it sees as different) that it does not.
type tagSE struct {
	E2 `json:"t"`
}

type wrapE struct{ err error }

func (w wrapE) Error() string { return "wrap" }
func (w wrapE) Unwrap() error { return w.err }

type multiE []error

func (m multiE) Error() string   { return "multi" }
func (m multiE) Unwrap() []error { return m }

// asE matches a *E3 target by its As method.
type asE struct{}

func (asE) Error() string { return "asE" }
func (asE) As(target any) bool {
	if p, ok := target.(*E3); ok {
		*p = 42
		return true
	}
	return false
}

// anyErr has the layout of the model's rtype (a struct of one field of type any): reflected on
// as in Go (only the go.layoutModelled rtype types themselves are opaque).
type anyErr struct{ v any }

func (anyErr) Error() string { return "anyErr" }

type chErr chan int

func (chErr) Error() string { return "chErr" }

type fnErr func(...int)

func (fnErr) Error() string { return "fnErr" }

type unwrapper interface{ Unwrap() error }
type myErrIface interface {
	error
	M()
}

func (E2) M() {}

type sameUnder1 []int
type sameUnder2 []int
type tagged1 struct {
	A int `json:"a"`
}

func typeCorpus() []any {
	return []any{
		tk[int](), tk[myInt](), tk[string](), tk[myString](), tk[*int](), tk[myPtr](), tk[**int](),
		tk[[]int](), tk[mySlice](), tk[sameUnder1](), tk[sameUnder2](), tk[map[string]int](),
		tk[myMap](), tk[[2]string](), tk[myArr](), tk[chan int](), tk[<-chan int](), tk[chan<- int](),
		tk[myChan](), tk[chErr](), tk[func() int](), tk[myFunc](), tk[func(...int)](), tk[func([]int)](),
		tk[fnErr](), tk[unsafe.Pointer](), tk[myUnsafe](),
		tk[struct{}](), tk[S](), tk[*S](), tk[impl](), tk[*impl](), tk[struct{ E2 }](), tk[SE](),
		tk[*struct{ E2 }](), tk[*SE](), tk[tagged1](), tk[struct {
			A int `json:"a"`
		}](), tk[struct{ A int }](),
		tk[G[int]](), tk[GP[int]](), tk[*G[int]](),
		tk[E1](), tk[*E1](), tk[E2](), tk[*E2](), tk[E3](), tk[E3b](), tk[*E3](), tk[wrapE](),
		tk[multiE](), tk[asE](), tk[anyErr](),
		tk[any](), tk[error](), tk[myIface](), tk[unwrapper](), tk[myErrIface](), tk[interface{ M() }](),
		tk[interface{ Error() string }](),
	}
}

// AssignableTo and Implements of the model against reflect's on every pair of the type corpus.
func TestReflectliteAssignable(t *testing.T) {
	l := newStuckLog(t)
	ts := typeCorpus()
	for _, vt := range ts {
		for _, tt := range ts {
			V, T := reflect.TypeOf(vt).Elem(), reflect.TypeOf(tt).Elem()
			name := V.String() + " to " + T.String()
			mV, mT := liteOf(vt), liteOf(tt)
			l.cmp("AssignableTo "+V.Kind().String()+"/"+T.Kind().String(), "AssignableTo("+name+")",
				run(func() any { return V.AssignableTo(T) }), run(func() any { return mV.AssignableTo(mT) }))
			l.cmp("Implements", "Implements("+name+")",
				run(func() any { return V.Implements(T) }), run(func() any { return mV.Implements(mT) }))
		}
		V := reflect.TypeOf(vt).Elem()
		mV := liteOf(vt)
		l.cmp("AssignableTo nil", "AssignableTo("+V.String()+", nil)", run(func() any { return V.AssignableTo(nil) }),
			run(func() any { return mV.AssignableTo(nil) }))
		l.cmp("Implements nil", "Implements("+V.String()+", nil)", run(func() any { return V.Implements(nil) }),
			run(func() any { return mV.Implements(nil) }))
	}
	l.finish()
	// the cases errors.As decides: a type implementing error against each target type
	for _, c := range []struct {
		v, t any
		want bool
	}{
		{tk[*E1](), tk[*E1](), true}, {tk[*E1](), tk[E2](), false}, {tk[E2](), tk[*E1](), false},
		{tk[E3](), tk[E3b](), false}, {tk[E2](), tk[SE](), false}, {tk[*E1](), tk[error](), true},
		{tk[E2](), tk[myErrIface](), true}, {tk[E3](), tk[myErrIface](), false},
		{tk[wrapE](), tk[unwrapper](), true}, {tk[*E1](), tk[*E2](), false},
	} {
		if got := liteOf(c.v).AssignableTo(liteOf(c.t)); got != c.want {
			t.Errorf("AssignableTo(%v, %v) = %v", reflect.TypeOf(c.v).Elem(), reflect.TypeOf(c.t).Elem(), got)
		}
	}
}

// errors.As (the real one, over the real reflectlite) against the real wrap.go over the model.
func TestErrorsAs(t *testing.T) {
	l := newStuckLog(t)
	e1 := &E1{"e1"}
	errs := map[string]error{
		"nil": nil, "*E1": e1, "E2": E2{}, "E3": E3(7), "E3b": E3b(8), "errors.New": errors.New("x"),
		"wrap(*E1)":        wrapE{e1},
		"wrap(wrap(E3))":   wrapE{wrapE{E3(9)}},
		"wrap(nil)":        wrapE{nil},
		"multi(nil, E2)":   multiE{nil, E2{}},
		"multi(E3b, *E1)":  multiE{E3b(1), e1},
		"asE":              asE{},
		"wrap(asE)":        wrapE{asE{}},
		"struct{E2}":       struct{ E2 }{},
		"SE":               SE{},
		"tagSE":            tagSE{},
		"anyErr":           anyErr{},
		"wrap(anyErr, E2)": multiE{anyErr{}, E2{}},
		"chErr":            chErr(nil),
		"fnErr":            fnErr(nil),
	}
	targets := map[string]func() any{
		"nil":         func() any { return nil },
		"**E1":        func() any { var p *E1; return &p },
		"*E2":         func() any { return new(E2) },
		"*E3":         func() any { return new(E3) },
		"*E3b":        func() any { return new(E3b) },
		"*error":      func() any { return new(error) },
		"*any":        func() any { return new(any) },
		"*unwrapper":  func() any { return new(unwrapper) },
		"*myErrIface": func() any { return new(myErrIface) },
		"*SE":         func() any { return new(SE) },
		"*struct{E2}": func() any { return new(struct{ E2 }) },
		"*struct{E2 t}": func() any {
			return new(struct {
				E2 `json:"t"`
			})
		},
		"*chErr":         func() any { return new(chErr) },
		"*fnErr":         func() any { return new(fnErr) },
		"*int":           func() any { return new(int) },
		"E2 (not ptr)":   func() any { return E2{} },
		"nil *E2":        func() any { return (*E2)(nil) },
		"nil **E1":       func() any { return (**E1)(nil) },
		"*[]int":         func() any { return new([]int) },
		"*interface{M}":  func() any { return new(interface{ M() }) },
		"*myPtr (named)": func() any { return new(myPtr) },
	}
	for en, err := range errs {
		for tn, mk := range targets {
			name := "As(" + en + ", " + tn + ")"
			tg, tm := mk(), mk()
			gO := run(func() any { return errors.As(err, tg) })
			mO := run(func() any { return em.As(err, tm) })
			if l.cmp("As", name, gO, mO) && tg != nil {
				if v := reflect.ValueOf(tg); v.Kind() == reflect.Pointer && !v.IsNil() {
					l.cmp("As", name+" *target", run(func() any { return v.Elem().Interface() }),
						run(func() any { return reflect.ValueOf(tm).Elem().Interface() }))
				}
			}
		}
	}
	// a Type as the target: Go's *rtype, the model's rtype (stuck)
	var goTy, mTy, mlTy any = reflect.TypeOf(0), rm.TypeOf(0), rlm.TypeOf(0)
	l.cmp("As Type target", "As(E2, TypeOf(0))", run(func() any { return errors.As(E2{}, goTy) }),
		run(func() any { return em.As(E2{}, mTy) }))
	l.cmp("As Type target", "As(E2, reflectlite TypeOf(0))", run(func() any { return errors.As(E2{}, goTy) }),
		run(func() any { return em.As(E2{}, mlTy) }))
	l.finish()
	tg := new(struct {
		E2 `json:"t"`
	})
	if !errors.As(tagSE{}, tg) {
		t.Errorf("Go: errors.As(tagSE{}, *struct{ E2 \"t\" }) is false")
	}
	if !stuck(func() { em.As(tagSE{}, tg) }) {
		t.Errorf("model: errors.As(tagSE{}, *struct{ E2 \"t\" }) not stuck")
	}
	if l.stuck["As Type target (Go panics)"] != 2 {
		t.Errorf("As with a Type target: not stuck")
	}
}
