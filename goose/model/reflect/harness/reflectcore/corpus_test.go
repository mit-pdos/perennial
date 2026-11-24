package reflectcore

import (
	"reflect"
	"runtime"
	"testing"
	"unsafe"
)

// The type corpus of the primitive tests.

func f1(int) string { return "" }

var anInt = 7
var aChan = make(chan int, 1)

type myInt int
type myInt8 int8
type myUint8 uint8
type myByte byte
type myString string
type myBool bool
type myFloat float64
type myBytes []byte
type myByteElems []myByte
type myPtr *int
type mySlice []int
type myMap map[string]int
type myFunc func(int) string
type myChan chan int
type myRecvChan <-chan int
type myUnsafe unsafe.Pointer
type myArr [3]int
type myIface interface{ M() }
type myAny any

type impl int

func (impl) M() {}

type ptrImpl struct{ n int }

func (*ptrImpl) M() {}

type Emb struct{ X int }
type EmbP struct{ Y int }

// S has exported, unexported, blank, embedded (value and pointer) and tagged fields.
type S struct {
	A int
	b string
	_ int
	Emb
	*EmbP
	C []int `json:"c"`
	d [2]byte
}

// S2 has S's underlying type.
type S2 S

type Tagged struct {
	A int `json:"a"`
}

type Plain struct {
	X int64
	Y uint32
	Z uint32
}

type Padded struct {
	X uint8
	Y int64
}

type G[T any] struct{ V T }
type Pair[K comparable, V any] struct {
	K K
	V V
}
type GSlice[T any] []T
type GPtr[T any] *T

type PS1 *S
type PS2 *S2

func tok[T any]() any { return (*T)(nil) }

// catch runs f and returns its panic value, if it panicked.
func catch(f func()) (p any, panicked bool) {
	panicked = true
	defer func() {
		if panicked {
			p = recover()
		}
	}()
	f()
	panicked = false
	return nil, false
}

func mustStuck(t *testing.T, what string, f func()) {
	t.Helper()
	p, ok := catch(f)
	if !ok {
		t.Errorf("%s: not stuck, returned", what)
	} else if !IsStuck(p) {
		t.Errorf("%s: panicked %v, want stuck", what, p)
	}
}

func mustStep(t *testing.T, what string, f func()) bool {
	t.Helper()
	if p, ok := catch(f); ok {
		t.Errorf("%s: panicked %v", what, p)
		return false
	}
	return true
}

func isRuntimeError(p any) bool {
	_, ok := p.(runtime.Error)
	return ok
}

// same is equality of two anys: dynamic types equal and values deeply equal, funcs by code
// pointer and nil-ness.
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

// entry is a corpus value x of static type T, with T's static instantiations of the helpers.
type entry struct {
	x     any
	typ   reflect.Type // T
	tok   any          // any((*T)(nil))
	ptrOK bool         // T is not an interface type
	// the helpers at T
	tokOf    func(any) any
	box      func(any) any
	load     func(any) any
	alloc    func(any) any
	ptrTok   func(any) any
	store    func(any, any)
	assertOk func(any) bool
	addr     func() any // any(&v) for a fresh v := x
}

func ent[T any](x T) entry {
	return entry{
		x: any(x), typ: reflect.TypeFor[T](), tok: tok[T](),
		ptrOK:    reflect.TypeFor[T]().Kind() != reflect.Interface,
		tokOf:    tokOf[T],
		box:      box[T],
		load:     load[T],
		alloc:    alloc[T],
		ptrTok:   ptrTok[T],
		store:    store[T],
		assertOk: assertOk[T],
		addr:     func() any { v := x; return &v },
	}
}

// corpus is one or more values per type constructor and predeclared type, named and unnamed,
// nil and not, structs with embedded, unexported, blank and tagged fields, arrays of length 0, 1
// and 3, generic instances; and values of interface types (their entries have ptrOK false: the
// dynamic type of any(x) is not T).
func corpus() []entry {
	s := S{A: 1, b: "b", Emb: Emb{2}, EmbP: &EmbP{3}, C: []int{4}, d: [2]byte{5, 6}}
	return []entry{
		ent(true), ent(myBool(false)),
		ent(int(-3)), ent(int8(-4)), ent(int16(5)), ent(int32(6)), ent(int64(-7)), ent(uint(8)),
		ent(uint8(9)), ent(uint16(10)), ent(uint32(11)), ent(uint64(12)), ent(uintptr(13)),
		ent(float32(1.5)), ent(float64(-2.5)), ent(complex64(1 + 2i)), ent(complex128(3 - 4i)),
		ent("str"), ent(""), ent(myInt(14)), ent(myInt8(-1)), ent(myUint8(2)), ent(myString("ms")),
		ent(myFloat(0.5)),
		ent([0]int{}), ent([1]string{"a"}), ent([3]int{1, 2, 3}), ent(myArr{4, 5, 6}),
		ent(aChan), ent((chan int)(nil)), ent((<-chan int)(aChan)), ent((chan<- int)(aChan)),
		ent(myChan(aChan)), ent(myRecvChan(aChan)),
		ent(f1), ent((func())(nil)), ent(myFunc(f1)), ent(myFunc(nil)),
		ent(map[string]int{"a": 1}), ent(map[int]bool{}), ent((map[string]int)(nil)),
		ent(myMap{"x": 2}), ent(myMap(nil)),
		ent(&anInt), ent((*int)(nil)), ent(myPtr(&anInt)), ent(myPtr(nil)), ent(&s), ent((*S)(nil)),
		ent([]int{1, 2}), ent([]int{}), ent([]int(nil)), ent(mySlice{3}), ent(mySlice(nil)),
		ent([]byte("bytes")), ent(myBytes("mb")),
		ent(struct{}{}), ent(s), ent(S2(s)), ent(Tagged{1}), ent(struct{ X, y int }{1, 2}),
		ent(struct {
			A int `json:"a"`
		}{3}),
		ent(unsafe.Pointer(&anInt)), ent(unsafe.Pointer(nil)), ent(myUnsafe(&anInt)),
		ent(impl(1)), ent(&ptrImpl{1}),
		ent(G[int]{1}), ent(G[string]{"g"}), ent(Pair[string, []int]{"k", nil}),
		ent(GSlice[int]{1}), ent(GPtr[int](&anInt)), ent(Plain{1, 2, 3}), ent(Padded{1, 2}),
		// interface-typed
		ent[any](3), ent[any](nil), ent[error](nil), ent[myIface](impl(2)), ent[myAny]("a"),
	}
}
