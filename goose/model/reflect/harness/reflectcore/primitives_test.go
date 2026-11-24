package reflectcore

// Per-primitive tests: each stub of core_harness.go (a GooseLang rule of
// Perennial/Golang/Defn/Reflect.lean, written over the real reflect) against the static Go
// operation the rule claims it is, over the corpus of corpus_test.go; and each stuck point of a
// rule where real Go panics, or where the rule is less defined than Go.

import (
	"reflect"
	"testing"
	"unsafe"
)

// FuncResolveAt's shapes give the type arguments that a Go compiler would infer from the
// dynamic type.
func TestShapeArgs(t *testing.T) {
	ty := reflect.TypeFor[int]()
	cases := []struct {
		s    Shape
		d    reflect.Type
		want []reflect.Type // nil: stuck
	}{
		{Self, reflect.TypeFor[myInt](), []reflect.Type{reflect.TypeFor[myInt]()}},
		{Shape{Kind: ShapeSlice}, reflect.TypeFor[mySlice](), []reflect.Type{reflect.TypeFor[mySlice](), ty}},
		{Shape{Kind: ShapeSlice}, reflect.TypeFor[[]string](), []reflect.Type{reflect.TypeFor[[]string](), reflect.TypeFor[string]()}},
		{Shape{Kind: ShapeSlice}, reflect.TypeFor[[3]int](), nil},
		{Shape{Kind: ShapeMap}, reflect.TypeFor[myMap](), []reflect.Type{reflect.TypeFor[myMap](), reflect.TypeFor[string](), ty}},
		{Shape{Kind: ShapeMap}, ty, nil},
		{Shape{Kind: ShapePtr}, reflect.TypeFor[myPtr](), []reflect.Type{reflect.TypeFor[myPtr](), ty}},
		{Shape{Kind: ShapePtr}, reflect.TypeFor[GPtr[string]](), []reflect.Type{reflect.TypeFor[GPtr[string]](), reflect.TypeFor[string]()}},
		{Shape{Kind: ShapePtr}, reflect.TypeFor[unsafe.Pointer](), nil},
		{Shape{Kind: ShapeChan, Dir: reflect.BothDir}, reflect.TypeFor[myChan](), []reflect.Type{reflect.TypeFor[myChan](), ty}},
		{Shape{Kind: ShapeChan, Dir: reflect.RecvDir}, reflect.TypeFor[myChan](), nil},
		{Shape{Kind: ShapeChan, Dir: reflect.RecvDir}, reflect.TypeFor[<-chan int](), []reflect.Type{reflect.TypeFor[<-chan int](), ty}},
		{DerefSelf, reflect.TypeFor[*myInt](), []reflect.Type{reflect.TypeFor[myInt]()}},
		{DerefSelf, reflect.TypeFor[**int](), []reflect.Type{reflect.TypeFor[*int]()}},
		{DerefSelf, reflect.TypeFor[myPtr](), nil},  // named: not syntactically *T
		{DerefSelf, reflect.TypeFor[GPtr[int]](), nil}, // a generic named pointer
		{DerefSelf, ty, nil},
		{Shape{Kind: ShapeDeref, Inner: &Shape{Kind: ShapeSlice}}, reflect.TypeFor[*mySlice](), []reflect.Type{reflect.TypeFor[mySlice](), ty}},
		{Shape{Kind: ShapeDeref, Inner: &Shape{Kind: ShapeMap}}, reflect.TypeFor[*map[int]bool](), []reflect.Type{reflect.TypeFor[map[int]bool](), ty, reflect.TypeFor[bool]()}},
	}
	for _, c := range cases {
		got, ok := ShapeArgs(c.s, c.d)
		if !ok {
			if c.want != nil {
				t.Errorf("ShapeArgs(%v, %v) none, want %v", c.s, c.d, c.want)
			}
			continue
		}
		if c.want == nil || !reflect.DeepEqual(got, c.want) {
			t.Errorf("ShapeArgs(%v, %v) = %v, want %v", c.s, c.d, got, c.want)
		}
	}
	mustStuck(t, "FuncResolveAt on nil", func() { FuncResolveAt([]Shape{Self}, "f", nil) })
	mustStuck(t, "FuncResolveAt arity", func() { FuncResolveAt([]Shape{Self, Self}, "f", 1) })
	if got := FuncResolveAt([]Shape{Self, {Kind: ShapeSlice}}, "f", 1, mySlice(nil)); !reflect.DeepEqual(got,
		[]reflect.Type{ty, reflect.TypeFor[mySlice](), ty}) {
		t.Errorf("FuncResolveAt two dispatch arguments: %v", got)
	}
}

// TokOf and Box (FuncResolveAt [self]) at the dynamic type are tokOf[T] and box[T] at the static
// type, for every non-interface corpus type; they are stuck on the nil interface.
func TestTokOfBox(t *testing.T) {
	for _, e := range corpus() {
		if !e.ptrOK {
			if e.x == nil {
				mustStuck(t, "TokOf(nil)", func() { TokOf(e.x) })
				mustStuck(t, "Box(nil)", func() { Box(e.x) })
			} else {
				// the dynamic type, not the interface type
				if TokOf(e.x) == e.tok {
					t.Errorf("TokOf of an interface-typed %v gave the interface's token", e.typ)
				}
			}
			continue
		}
		if got := TokOf(e.x); got != e.tokOf(e.x) || got != e.tok {
			t.Errorf("TokOf(%v) = %#v, tokOf[%v] = %#v, want %#v", e.typ, got, e.typ, e.tokOf(e.x), e.tok)
		}
		b, sb := Box(e.x), e.box(e.x)
		if reflect.TypeOf(b) != reflect.PointerTo(e.typ) || reflect.TypeOf(sb) != reflect.TypeOf(b) {
			t.Errorf("Box(%v): type %T, box: %T", e.typ, b, sb)
			continue
		}
		if !same(reflect.ValueOf(b).Elem().Interface(), e.x) || !same(e.load(b), e.x) {
			t.Errorf("Box(%v): *b = %v, want %v", e.typ, reflect.ValueOf(b).Elem(), e.x)
		}
		if e.typ.Size() > 0 && reflect.ValueOf(b).Pointer() == reflect.ValueOf(Box(e.x)).Pointer() {
			t.Errorf("Box(%v) twice gave one address", e.typ)
		}
	}
}

// Load, Alloc and PtrTok (FuncResolveAt [deref self]) on any(&v), v : T, are load[T], alloc[T]
// and ptrTok[T]; Alloc and PtrTok also take a token. Load of a nil *T is Go's nil dereference.
// They are stuck on nil, a named pointer type and a non-pointer.
func TestLoadAllocPtrTok(t *testing.T) {
	for _, e := range corpus() {
		p := e.addr()
		if got, want := Load(p), e.load(p); !same(got, want) || !same(got, e.x) {
			t.Errorf("Load(*%v) = %#v, load = %#v, want %#v", e.typ, got, want, e.x)
		}
		for _, arg := range []any{p, e.tok} {
			a, sa := Alloc(arg), e.alloc(arg)
			if reflect.TypeOf(a) != reflect.PointerTo(e.typ) || reflect.TypeOf(sa) != reflect.TypeOf(a) {
				t.Errorf("Alloc(%T) = %T, alloc = %T", arg, a, sa)
				continue
			}
			if !reflect.ValueOf(a).Elem().IsZero() {
				t.Errorf("Alloc(%T): not zero", arg)
			}
			if got := PtrTok(arg); got != e.ptrTok(arg) || got != Token(reflect.PointerTo(e.typ)) {
				t.Errorf("PtrTok(%T) = %#v", arg, got)
			}
		}
		if e.typ.Size() > 0 && reflect.ValueOf(Alloc(p)).Pointer() == reflect.ValueOf(p).Pointer() {
			t.Errorf("Alloc(*%v) returned its argument", e.typ)
		}
		// nil *T: Go's nil dereference in both
		p1, ok1 := catch(func() { Load(e.tok) })
		p2, ok2 := catch(func() { e.load(e.tok) })
		if !ok1 || !ok2 || !isRuntimeError(p1) || !isRuntimeError(p2) {
			t.Errorf("Load of a nil *%v: %v %v, load: %v %v", e.typ, ok1, p1, ok2, p2)
		}
	}
	for _, f := range []func(any) any{Load, Alloc, PtrTok} {
		mustStuck(t, "deref self on nil", func() { f(nil) })
		mustStuck(t, "deref self on a named pointer", func() { f(myPtr(&anInt)) })
		mustStuck(t, "deref self on a generic named pointer", func() { f(GPtr[int](&anInt)) })
		mustStuck(t, "deref self on an int", func() { f(3) })
		mustStuck(t, "deref self on unsafe.Pointer", func() { f(unsafe.Pointer(&anInt)) })
	}
	// an interface-typed variable: load gives its dynamic value
	var i myIface = impl(4)
	if got := Load(&i); got != any(impl(4)) {
		t.Errorf("Load(*myIface) = %#v", got)
	}
	var n error
	if got := Load(&n); got != nil {
		t.Errorf("Load(*error) of nil = %#v", got)
	}
}

// FieldRefAt(any(&s), i) is any(&s.f_i): the same address, so writes through it reach s, for
// exported, unexported and embedded (value and pointer) fields and generic instances; stuck on
// a blank field, an out-of-range index, a nil pointer, a named pointer type and a non-struct.
func TestFieldRefAt(t *testing.T) {
	s := S{A: 1, b: "b", Emb: Emb{2}, EmbP: &EmbP{3}, C: []int{4}, d: [2]byte{5, 6}}
	want := []any{&s.A, &s.b, nil, &s.Emb, &s.EmbP, &s.C, &s.d}
	for i, w := range want {
		if w == nil {
			mustStuck(t, "FieldRefAt blank field", func() { FieldRefAt(&s, i) })
			continue
		}
		if got := FieldRefAt(&s, i); got != w {
			t.Errorf("FieldRefAt(&s, %d) = %#v, want %#v", i, got, w)
		}
	}
	*FieldRefAt(&s, 0).(*int) = 10
	*FieldRefAt(&s, 1).(*string) = "bb"
	FieldRefAt(&s, 3).(*Emb).X = 20
	*FieldRefAt(&s, 4).(**EmbP) = &EmbP{30}
	(*FieldRefAt(&s, 6).(*[2]byte))[1] = 60
	if s.A != 10 || s.b != "bb" || s.X != 20 || s.Y != 30 || s.d[1] != 60 {
		t.Errorf("writes through FieldRefAt did not reach s: %+v", s)
	}
	// the embedded field's own fields, through the embedded struct's address
	if FieldRefAt(FieldRefAt(&s, 3), 0) != any(&s.X) {
		t.Errorf("FieldRefAt of an embedded field's field")
	}
	g := Pair[string, []int]{"k", nil}
	if FieldRefAt(&g, 1) != any(&g.V) {
		t.Errorf("FieldRefAt of a generic instance")
	}
	var anon struct{ x, Y int }
	if FieldRefAt(&anon, 1) != any(&anon.Y) {
		t.Errorf("FieldRefAt of an unnamed struct")
	}
	mustStuck(t, "FieldRefAt index -1", func() { FieldRefAt(&s, -1) })
	mustStuck(t, "FieldRefAt index n", func() { FieldRefAt(&s, 7) })
	mustStuck(t, "FieldRefAt nil pointer", func() { FieldRefAt((*S)(nil), 0) })
	mustStuck(t, "FieldRefAt named pointer", func() { FieldRefAt(PS1(&s), 0) })
	mustStuck(t, "FieldRefAt non-struct", func() { FieldRefAt(&anInt, 0) })
	mustStuck(t, "FieldRefAt struct value", func() { FieldRefAt(s, 0) })
	mustStuck(t, "FieldRefAt nil", func() { FieldRefAt(nil, 0) })
	mustStuck(t, "FieldRefAt empty struct", func() { FieldRefAt(&struct{}{}, 0) })
}

// ArraySliceAt(any(&a)) is any(a[:]): len = cap = n, the element addresses of a, writes reach a;
// for n = 0 a non-nil empty slice, as Go's; stuck on nil and a non-array.
func TestArraySliceAt(t *testing.T) {
	a := [3]int{1, 2, 3}
	s := ArraySliceAt(&a).([]int)
	if len(s) != 3 || cap(s) != 3 || &s[0] != &a[0] || &s[2] != &a[2] {
		t.Errorf("ArraySliceAt([3]int): %v len %d cap %d", s, len(s), cap(s))
	}
	s[1] = 20
	if a[1] != 20 {
		t.Errorf("write through ArraySliceAt did not reach the array")
	}
	ma := myArr{4, 5, 6}
	if ms := ArraySliceAt(&ma).([]int); &ms[0] != &ma[0] || len(ms) != 3 {
		t.Errorf("ArraySliceAt(myArr) = %v", ms)
	}
	one := [1]string{"x"}
	if os := ArraySliceAt(&one).([]string); len(os) != 1 || cap(os) != 1 || &os[0] != &one[0] {
		t.Errorf("ArraySliceAt([1]string) = %v", os)
	}
	var z [0]int
	zs := ArraySliceAt(&z).([]int)
	static := z[:]
	if zs == nil || len(zs) != 0 || cap(zs) != 0 || static == nil {
		t.Errorf("ArraySliceAt([0]int): nil %v, static nil %v", zs == nil, static == nil)
	}
	if unsafe.SliceData(zs) != unsafe.SliceData(static) {
		t.Errorf("ArraySliceAt([0]int): another data pointer than z[:]")
	}
	type structs [2]struct{ X int }
	var sa structs
	ArraySliceAt(&sa).([]struct{ X int })[1].X = 7
	if sa[1].X != 7 {
		t.Errorf("ArraySliceAt of a named array of structs")
	}
	mustStuck(t, "ArraySliceAt nil", func() { ArraySliceAt((*[3]int)(nil)) })
	mustStuck(t, "ArraySliceAt non-array", func() { ArraySliceAt(&anInt) })
	mustStuck(t, "ArraySliceAt slice", func() { ArraySliceAt(&[]int{}) })
	mustStuck(t, "ArraySliceAt array value", func() { ArraySliceAt(a) })
}

// EqNilAt(any(x)) is x == nil at x's type for pointer, slice, map, chan, func and unsafe.Pointer
// types, named or not, nil, non-nil and non-nil empty; stuck on other kinds and on the nil
// interface.
func TestEqNilAt(t *testing.T) {
	var (
		np  *int
		ns  []int
		nm  map[string]int
		nc  chan int
		nf  func()
		nu  unsafe.Pointer
		nmp myPtr
		nms mySlice
		nmm myMap
		nmc myChan
		nmf myFunc
		nmu myUnsafe
		ngp GPtr[int]
	)
	es, em := []int{}, map[string]int{}
	ms0, mm0 := make([]int, 0), make(map[int]int)
	ch := make(chan int)
	cases := []struct {
		x    any
		want bool
	}{
		{np, np == nil}, {ns, ns == nil}, {nm, nm == nil}, {nc, nc == nil}, {nf, nf == nil},
		{nu, nu == nil}, {nmp, nmp == nil}, {nms, nms == nil}, {nmm, nmm == nil},
		{nmc, nmc == nil}, {nmf, nmf == nil}, {nmu, nmu == nil}, {ngp, ngp == nil},
		{&anInt, false}, {es, es == nil}, {em, em == nil}, {ms0, ms0 == nil}, {mm0, mm0 == nil},
		{ch, ch == nil}, {f1, false}, {myFunc(f1), false}, {unsafe.Pointer(&anInt), false},
		{(<-chan int)(ch), false}, {es[:0], es[:0] == nil}, {ns[:0], ns[:0] == nil},
	}
	for _, c := range cases {
		if got := EqNilAt(c.x); got != c.want {
			t.Errorf("EqNilAt(%T) = %v, want %v", c.x, got, c.want)
		}
		if got := reflect.ValueOf(c.x).IsNil(); got != c.want {
			t.Errorf("reflect IsNil(%T) = %v, want %v", c.x, got, c.want)
		}
	}
	if !(es != nil && ms0 != nil && em != nil && mm0 != nil && ns[:0] == nil) {
		t.Errorf("gc: non-nil empty slices and maps")
	}
	for _, x := range []any{0, "", struct{}{}, [0]int{}, true, 1.5, impl(1), S{}} {
		mustStuck(t, "EqNilAt "+reflect.TypeOf(x).String(), func() { EqNilAt(x) })
	}
	mustStuck(t, "EqNilAt nil interface", func() { EqNilAt(nil) })
}

// PointerOfAt is reflect's UnsafePointer for each row: a pointer's address, an unsafe.Pointer, a
// slice's data pointer, a map's and a chan's; stuck on a func and other kinds.
func TestPointerOfAt(t *testing.T) {
	p := &anInt
	m := map[int]int{1: 1}
	ch := make(chan int)
	sl := []int{1, 2, 3}
	arr := [3]int{}
	cases := []struct {
		name string
		x    any
		want unsafe.Pointer
	}{
		{"*int", p, unsafe.Pointer(p)},
		{"nil *int", (*int)(nil), nil},
		{"myPtr", myPtr(p), unsafe.Pointer(p)},
		{"unsafe.Pointer", unsafe.Pointer(p), unsafe.Pointer(p)},
		{"myUnsafe", myUnsafe(p), unsafe.Pointer(p)},
		{"[]int", sl, unsafe.Pointer(unsafe.SliceData(sl))},
		{"[]int[1:]", sl[1:], unsafe.Pointer(&sl[1])},
		{"mySlice", mySlice(sl), unsafe.Pointer(&sl[0])},
		{"nil []int", []int(nil), nil},
		{"array slice", arr[:], unsafe.Pointer(&arr[0])},
		{"map", m, reflect.ValueOf(m).UnsafePointer()},
		{"nil map", map[int]int(nil), nil},
		{"chan", ch, reflect.ValueOf(ch).UnsafePointer()},
		{"nil chan", (chan int)(nil), nil},
	}
	for _, c := range cases {
		if got := PointerOfAt(c.x); got != c.want || got != reflect.ValueOf(c.x).UnsafePointer() {
			t.Errorf("PointerOfAt(%s) = %v, want %v", c.name, got, c.want)
		}
	}
	m2 := m
	if PointerOfAt(m2) != PointerOfAt(m) || PointerOfAt(map[int]int{}) == PointerOfAt(m) {
		t.Errorf("PointerOfAt of a map is not its identity")
	}
	mustStuck(t, "PointerOfAt func", func() { PointerOfAt(f1) })
	mustStuck(t, "PointerOfAt nil func", func() { PointerOfAt((func())(nil)) })
	mustStuck(t, "PointerOfAt int", func() { PointerOfAt(1) })
	mustStuck(t, "PointerOfAt string", func() { PointerOfAt("s") })
	mustStuck(t, "PointerOfAt nil", func() { PointerOfAt(nil) })
}

// What gc gives for the data pointer of empty slices, against the Lean slice row (s.ptr). Lean:
// a nil slice's ptr is null; make([]T, 0) and every cap-0 make give an arbitrary non-null
// address (GoPrealloc, gc's zerobase); a[i:j] has ptr &a[i] (arrayIndexRef), also when the
// result's cap is 0. gc does not advance the pointer when the result's cap is 0, so for a[n:]
// of an array of n elements gc gives &a[0] where Lean gives &a[n] (one past the end).
func TestPointerOfAtEmptySlices(t *testing.T) {
	lit, mk, mk0 := []int{}, make([]int, 0), make([]int, 0, 0)
	pl, pm, pm0 := PointerOfAt(lit), PointerOfAt(mk), PointerOfAt(mk0)
	t.Logf("gc: []int{} %p, make([]int,0) %p, make([]int,0,0) %p", pl, pm, pm0)
	if pl == nil || pm == nil || pm0 == nil {
		t.Errorf("gc gives a nil data pointer for a non-nil empty slice")
	}
	if pl != pm || pm != pm0 {
		t.Logf("gc: the empty slices have different data pointers")
	}
	var a [3]int
	end := a[3:]
	t.Logf("gc: a[3:] of [3]int: %p, &a[0] %p, &a[2] %p", PointerOfAt(end), &a[0], &a[2])
	if PointerOfAt(end) != unsafe.Pointer(&a[0]) {
		t.Errorf("gc: a[3:] data pointer is not &a[0]")
	}
	s := []int{1, 2}
	if PointerOfAt(s[2:]) != unsafe.Pointer(&s[0]) || PointerOfAt(s[1:1]) != unsafe.Pointer(&s[1]) {
		t.Errorf("gc: s[len:] (cap 0) not at &s[0], or s[1:1] (cap 1) not at &s[1]")
	}
}
