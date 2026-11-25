package reflectcore

import (
	"math"
	"reflect"
	"sort"
	"testing"
	"unsafe"
)

// A ConvertAt case: x converted to the type of the token to.
type cvCase struct {
	name string
	x    any
	to   any
	goOK bool // a legal Go conversion; want is any(U(x)), written statically
	want any
	lean bool // a Lean Convert rule steps (the harness ConvertAt steps)
}

type integer interface {
	~int | ~int8 | ~int16 | ~int32 | ~int64 | ~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64 | ~uintptr
}

func ic[F, T integer](x F) cvCase {
	return cvCase{name: reflect.TypeFor[F]().String() + "->" + reflect.TypeFor[T]().String(),
		x: x, to: tok[T](), goOK: true, want: T(x), lean: true}
}

func intPairs[F integer](x F) []cvCase {
	return []cvCase{ic[F, int](x), ic[F, int8](x), ic[F, int16](x), ic[F, int32](x),
		ic[F, int64](x), ic[F, uint](x), ic[F, uint8](x), ic[F, uint16](x), ic[F, uint32](x),
		ic[F, uint64](x), ic[F, uintptr](x), ic[F, myInt](x), ic[F, myInt8](x), ic[F, myUint8](x)}
}

func intCases() []cvCase {
	var cs []cvCase
	for _, v := range []int64{0, 1, -1, 127, 128, 255, 256, -129, 65535, 1 << 31, -1 << 31,
		1<<32 + 5, math.MaxInt64, math.MinInt64} {
		cs = append(cs, intPairs(int(v))...)
		cs = append(cs, intPairs(int8(v))...)
		cs = append(cs, intPairs(int16(v))...)
		cs = append(cs, intPairs(int32(v))...)
		cs = append(cs, intPairs(v)...)
		cs = append(cs, intPairs(uint(v))...)
		cs = append(cs, intPairs(uint8(v))...)
		cs = append(cs, intPairs(uint16(v))...)
		cs = append(cs, intPairs(uint32(v))...)
		cs = append(cs, intPairs(uint64(v))...)
		cs = append(cs, intPairs(uintptr(v))...)
		cs = append(cs, intPairs(myInt(v))...)
		cs = append(cs, intPairs(myInt8(v))...)
		cs = append(cs, intPairs(myUint8(v))...)
	}
	return cs
}

func bs[F ~uint8, T ~string](x F) cvCase {
	return cvCase{name: "byte->string", x: x, to: tok[T](), goOK: true, want: T(x), lean: true}
}

func byteStringCases() []cvCase {
	var cs []cvCase
	for _, c := range []uint8{0, 65, 127, 128, 200, 255} {
		cs = append(cs, bs[uint8, string](c), bs[myUint8, string](myUint8(c)),
			bs[myByte, myString](myByte(c)), bs[uint8, myString](c))
	}
	return cs
}

type S1 struct{ A int }
type S1b S1
type PS1x *S1

// One conversion: hand-written cases of each rule family and of each pair that reflect's
// convertOp accepts, with the static conversion as want.
func explicitCases() []cvCase {
	s := S{A: 1, b: "b", C: []int{2}}
	p := &anInt
	sl := []int{1, 2}
	m := map[string]int{"a": 1}
	var ip any = p
	bothCh := make(chan int)
	var sendCh chan<- int = bothCh
	r65, r0x10ffff, i64 := rune(65), rune(0x10ffff), int64(66)
	f64, f32 := 2.75, float32(-1.5)
	c128 := complex(1, 2)
	arr3 := []int{1, 2, 3}
	type T1 = struct{ A int }
	return []cvCase{
		// identical underlying types (cvtDirect)
		{"myInt->int", myInt(3), tok[int](), true, int(myInt(3)), true},
		{"mySlice->[]int", mySlice(sl), tok[[]int](), true, []int(mySlice(sl)), true},
		{"[]int->mySlice", sl, tok[mySlice](), true, mySlice(sl), true},
		{"myMap->map", myMap(m), tok[map[string]int](), true, map[string]int(myMap(m)), true},
		{"myFunc->func", myFunc(f1), tok[func(int) string](), true, (func(int) string)(myFunc(f1)), true},
		{"myArr->[3]int", myArr{1, 2, 3}, tok[[3]int](), true, [3]int(myArr{1, 2, 3}), true},
		{"myString->string", myString("a"), tok[string](), true, string(myString("a")), true},
		{"myBool->bool", myBool(true), tok[bool](), true, bool(myBool(true)), true},
		{"myFloat->float64", myFloat(0.5), tok[float64](), true, float64(myFloat(0.5)), true},
		{"S->S2", s, tok[S2](), true, S2(s), true},
		{"S1->struct{A int}", S1{4}, tok[T1](), true, T1(S1{4}), true},
		{"struct{A int}->S1b", T1{5}, tok[S1b](), true, S1b(T1{5}), true},
		{"G[int]->struct{V int}", G[int]{6}, tok[struct{ V int }](), true, struct{ V int }(G[int]{6}), true},
		{"myPtr->*int", myPtr(p), tok[*int](), true, (*int)(myPtr(p)), true},
		{"*int->myPtr", p, tok[myPtr](), true, myPtr(p), true},
		{"myChan->chan int", myChan(bothCh), tok[chan int](), true, (chan int)(myChan(bothCh)), true},
		{"myUnsafe->unsafe.Pointer", myUnsafe(p), tok[unsafe.Pointer](), true, unsafe.Pointer(myUnsafe(p)), true},
		// tags: a defined struct type's underlying type has no tags in Lean
		{"Tagged->struct{A int}", Tagged{1}, tok[T1](), true, T1(Tagged{1}), true},
		{"struct{A int}->Tagged", T1{1}, tok[Tagged](), true, Tagged(T1{1}), true},
		{"Tagged->struct{A int `json:\"a\"`}", Tagged{1}, tok[struct {
			A int `json:"a"`
		}](), true, struct {
			A int `json:"a"`
		}(Tagged{1}), false},
		{"struct{A int `json:\"a\"`}->struct{A int}", struct {
			A int `json:"a"`
		}{2}, tok[T1](), true, T1(struct {
			A int `json:"a"`
		}{2}), false},
		// unnamed pointers with identical underlying base types
		{"*myInt->*int", (*myInt)(p), tok[*int](), true, (*int)((*myInt)(p)), true},
		{"*S->*S2", &s, tok[*S2](), true, (*S2)(&s), true},
		{"*S1->*struct{A int}", &S1{1}, tok[*T1](), true, nil, true},
		// channels from a bidirectional channel
		{"chan int-><-chan int", bothCh, tok[<-chan int](), true, (<-chan int)(bothCh), true},
		{"chan int->chan<- int", bothCh, tok[chan<- int](), true, (chan<- int)(bothCh), true},
		{"myChan-><-chan int", myChan(bothCh), tok[<-chan int](), true, (<-chan int)(myChan(bothCh)), true},
		{"chan int->myRecvChan", bothCh, tok[myRecvChan](), true, myRecvChan(bothCh), true},
		// strings and bytes
		{"string->[]byte", "héllo", tok[[]byte](), true, []byte("héllo"), true},
		{"[]byte->string", []byte("abc"), tok[string](), true, string([]byte("abc")), true},
		{"myBytes->myString", myBytes("x"), tok[myString](), true, myString(myBytes("x")), true},
		{"myString->myBytes", myString("y"), tok[myBytes](), true, myBytes(myString("y")), true},
		{"string->[]myByte", "z", tok[myByteElems](), true, myByteElems("z"), true},
		{"[]myByte->string", myByteElems{'w'}, tok[string](), true, string(myByteElems{'w'}), true},
		// unsafe.Pointer
		{"*int->unsafe.Pointer", p, tok[unsafe.Pointer](), true, unsafe.Pointer(p), true},
		{"unsafe.Pointer->*int", unsafe.Pointer(p), tok[*int](), true, (*int)(unsafe.Pointer(p)), true},
		{"unsafe.Pointer->*Plain", unsafe.Pointer(&Plain{}), tok[*Plain](), true, nil, true},
		{"nil unsafe.Pointer->*string", unsafe.Pointer(nil), tok[*string](), true, (*string)(unsafe.Pointer(nil)), true},
		{"unsafe.Pointer->*string (not plain)", unsafe.Pointer(&s.b), tok[*string](), true, (*string)(unsafe.Pointer(&s.b)), false},
		{"unsafe.Pointer->*Padded (not plain)", unsafe.Pointer(&Padded{}), tok[*Padded](), true, nil, false},
		{"unsafe.Pointer->uintptr", unsafe.Pointer(p), tok[uintptr](), true, uintptr(unsafe.Pointer(p)), true},
		// to an interface the value implements: the value itself
		{"int->any", 3, tok[any](), true, any(3), true},
		{"impl->myIface", impl(1), tok[myIface](), true, any(myIface(impl(1))), true},
		{"*ptrImpl->myIface", &ptrImpl{}, tok[myIface](), true, nil, true},
		{"*int->any", p, tok[any](), true, ip, true},
		{"myInt->myAny", myInt(1), tok[myAny](), true, any(myAny(myInt(1))), true},
		// integers and floats (convert_<int>_to_float64/32, convert_float64/32_to_integer, ...)
		{"float64->int", f64, tok[int](), true, int(f64), true},
		{"int->float64", 3, tok[float64](), true, float64(3), true},
		{"float64->float32", f64, tok[float32](), true, float32(f64), true},
		{"float32->float64", f32, tok[float64](), true, float64(f32), true},
		{"float64->uint8", f64, tok[uint8](), true, uint8(f64), true},
		// legal Go, no Lean Convert rule (less defined: fine)
		{"rune->string", r65, tok[string](), true, string(r65), false},
		{"rune max->string", r0x10ffff, tok[string](), true, string(r0x10ffff), false},
		{"int64->string", i64, tok[string](), true, "B", false},
		{"string->[]rune", "hé", tok[[]rune](), true, []rune("hé"), false},
		{"[]rune->string", []rune("hé"), tok[string](), true, string([]rune("hé")), false},
		{"complex128->complex64", c128, tok[complex64](), true, complex64(c128), false},
		{"[]int->[3]int", arr3, tok[[3]int](), true, [3]int(arr3), false},
		{"[]int->*[3]int", arr3, tok[*[3]int](), true, nil, false},
		// not legal Go
		{"int->[]int", 1, tok[[]int](), false, nil, false},
		{"string->int", "1", tok[int](), false, nil, false},
		{"bool->int", true, tok[int](), false, nil, false},
		{"int->bool", 1, tok[bool](), false, nil, false},
		{"S1->S", S1{}, tok[S](), false, nil, false},
		{"map->slice", m, tok[[]int](), false, nil, false},
		{"func->int", f1, tok[int](), false, nil, false},
		{"int->myIface", 1, tok[myIface](), false, nil, false},
		{"ptrImpl->myIface", ptrImpl{}, tok[myIface](), false, nil, false},
		{"[]int->[]int64", sl, tok[[]int64](), false, nil, false},
		{"*int->*int64", p, tok[*int64](), false, nil, false},
		{"[]myInt->string", []myInt{1}, tok[string](), false, nil, false},
		{"[]byte->[4]int", []byte{1}, tok[[4]int](), false, nil, false},
		// not legal Go, and no Lean Convert rule steps (etcd-grove#59: the channel rules take a
		// bidirectional channel and an unnamed side, the pointer rule unnamed pointer types)
		{"<-chan int->chan<- int", (<-chan int)(bothCh), tok[chan<- int](), false, nil, false},
		{"chan<- int-><-chan int", sendCh, tok[<-chan int](), false, nil, false},
		{"chan<- int->chan int", sendCh, tok[chan int](), false, nil, false},
		{"myChan->myRecvChan (both named)", myChan(bothCh), tok[myRecvChan](), false, nil, false},
		{"PS1x->*S1b (named pointer)", PS1x(&S1{}), tok[*S1b](), false, nil, false},
		{"PS1x->*struct{A int} (named pointer)", PS1x(&S1{}), tok[*T1](), false, nil, false},
	}
}

// leanOnly are the conversions ConvertAt performs that Go does not allow: none, since no Convert
// rule steps on one (TestConvertLeanRules).
var leanOnly []string

// ConvertAt is, wherever a Lean Convert rule steps and Go allows the conversion, any(U(x)) of the
// static conversion, and agrees with reflect's Value.Convert where convertOp accepts the pair;
// where Go does not allow the conversion, reflect's Convert panics and ConvertAt is stuck,
// except on leanOnly.
func TestConvertAt(t *testing.T) {
	cases := append(append(intCases(), byteStringCases()...), explicitCases()...)
	var gotLeanOnly, lessDefined []string
	for _, c := range cases {
		var res any
		p, panicked := catch(func() { res = ConvertAt(c.x, c.to) })
		if panicked && !IsStuck(p) {
			t.Errorf("%s: ConvertAt panicked %v", c.name, p)
			continue
		}
		u := reflect.TypeOf(c.to).Elem()
		_, rpanicked := catch(func() { reflect.ValueOf(c.x).Convert(u) })
		reflectOK := !rpanicked
		switch {
		case c.lean && panicked:
			t.Errorf("%s: stuck, want a step", c.name)
		case !c.lean && !panicked:
			t.Errorf("%s: stepped to %#v, want stuck", c.name, res)
		case c.lean && c.goOK:
			if c.want != nil && !same(res, c.want) {
				t.Errorf("%s: ConvertAt = %#v, want %#v", c.name, res, c.want)
			}
			if reflect.TypeOf(res) != u && u.Kind() != reflect.Interface {
				t.Errorf("%s: result type %T", c.name, res)
			}
			if reflectOK {
				if r := reflect.ValueOf(c.x).Convert(u).Interface(); !same(r, res) && u.Kind() != reflect.UnsafePointer {
					t.Errorf("%s: reflect Convert = %#v, ConvertAt = %#v", c.name, r, res)
				}
			}
		case c.lean && !c.goOK:
			gotLeanOnly = append(gotLeanOnly, c.name)
			if reflectOK {
				t.Errorf("%s: reflect converts a pair the test calls illegal", c.name)
			}
		case !c.lean && c.goOK:
			lessDefined = append(lessDefined, c.name)
		case !c.lean && !c.goOK:
			if reflectOK {
				t.Errorf("%s: reflect converts a pair the test calls illegal", c.name)
			}
		}
	}
	sort.Strings(gotLeanOnly)
	if len(gotLeanOnly) != len(leanOnly) || len(gotLeanOnly) > 0 && !reflect.DeepEqual(gotLeanOnly, leanOnly) {
		t.Errorf("Lean-only conversions %q, want %q", gotLeanOnly, leanOnly)
	}
	t.Logf("more defined than Go (Lean steps, Go rejects): %q", gotLeanOnly)
	t.Logf("less defined than Go (Go converts, Lean stuck): %q", lessDefined)
}

// The pairs reflect's convertOp accepts that Go also accepts but that have no Lean rule; and the
// pairs Lean and Go accept but reflect's convertOp rejects (so the model never converts them).
func TestConvertOpVsLean(t *testing.T) {
	var reflectNoLean, leanNoReflect []string
	for _, c := range append(append(intCases(), byteStringCases()...), explicitCases()...) {
		if !c.goOK {
			continue
		}
		u := reflect.TypeOf(c.to).Elem()
		r := reflect.TypeOf(c.x).ConvertibleTo(u)
		if r && !c.lean {
			reflectNoLean = append(reflectNoLean, c.name)
		}
		if !r && c.lean {
			leanNoReflect = append(leanNoReflect, c.name)
		}
	}
	t.Logf("convertOp accepts, no Lean rule (model stuck where Go converts): %q", reflectNoLean)
	t.Logf("Lean rule, convertOp rejects: %q", leanNoReflect)
}

// ConvertAt keeps a reference's identity: the same pointer, the same backing array, the same map.
func TestConvertAtIdentity(t *testing.T) {
	x := 1
	p := &x
	q := ConvertAt(myPtr(p), tok[*int]()).(*int)
	if q != p {
		t.Errorf("myPtr->*int: %p, want %p", q, p)
	}
	if r := ConvertAt(p, tok[*myInt]()).(*myInt); unsafe.Pointer(r) != unsafe.Pointer(p) {
		t.Errorf("*int->*myInt: another pointer")
	}
	sl := mySlice{1, 2}
	s2 := ConvertAt(sl, tok[[]int]()).([]int)
	s2[0] = 9
	if sl[0] != 9 {
		t.Errorf("mySlice->[]int: a copy")
	}
	m := myMap{}
	m2 := ConvertAt(m, tok[map[string]int]()).(map[string]int)
	m2["k"] = 1
	if m["k"] != 1 {
		t.Errorf("myMap->map: a copy")
	}
	var i any = p
	if ConvertAt(p, tok[any]()) != i {
		t.Errorf("*int->any: not the value itself")
	}
	// []byte(s) is a copy in Go and in Lean
	b := []byte("ab")
	str := ConvertAt(b, tok[string]()).(string)
	b[0] = 'z'
	if str != "ab" {
		t.Errorf("[]byte->string aliases")
	}
	mustStuck(t, "ConvertAt(nil, tok)", func() { ConvertAt(nil, tok[int]()) })
	mustStuck(t, "ConvertAt(x, nil)", func() { ConvertAt(1, nil) })
	mustStuck(t, "ConvertAt(x, named pointer token)", func() { ConvertAt(1, myPtr(nil)) })
	mustStuck(t, "ConvertAt(x, non-pointer)", func() { ConvertAt(1, 2) })
}

// goLegal is Go's conversion rules for a non-constant value of type t to type u, as the run time
// has them: reflect's ConvertibleTo, and the unsafe.Pointer rules of package unsafe, which
// reflect's convertOp lacks (a pointer or uintptr to and from unsafe.Pointer). Where it differs
// from the spec it is narrower (convertOp: a []E to string only for an unnamed E), never wider.
func goLegal(t, u reflect.Type) bool {
	tk, uk := t.Kind(), u.Kind()
	ptrOrUintptr := func(k reflect.Kind) bool { return k == reflect.Pointer || k == reflect.Uintptr }
	return t.ConvertibleTo(u) ||
		ptrOrUintptr(tk) && uk == reflect.UnsafePointer ||
		tk == reflect.UnsafePointer && ptrOrUintptr(uk)
}

// The Lean Convert rules themselves (convertLean) are no more defined than Go (CRITERIA.md,
// "Every Convert rule steps only on a conversion Go allows"; ConvertAt relies on it): on every
// case, where a rule steps, the case says the static conversion is legal Go; and on every pair of
// corpus types (at the zero value), where a rule steps, or ConvertAt steps (interface targets
// too), goLegal holds. The witnesses of etcd-grove#59 are cases above: each is stuck.
func TestConvertLeanRules(t *testing.T) {
	for _, c := range append(append(intCases(), byteStringCases()...), explicitCases()...) {
		u := reflect.TypeOf(c.to).Elem()
		if u.Kind() == reflect.Interface {
			continue // ConvertAt's interface row: TestConvertAt
		}
		_, ok := convertLean(reflect.ValueOf(c.x), u)
		if ok && !c.goOK {
			t.Errorf("%s: a Lean Convert rule steps, but not legal Go", c.name)
		}
	}
	es := corpus()
	nLean, nAt, nGo := 0, 0, 0
	for _, e := range es {
		for _, f := range es {
			tt, u := e.typ, f.typ
			if goLegal(tt, u) {
				nGo++
			}
			if _, ok := convertLean(reflect.Zero(tt), u); ok {
				nLean++
				if !goLegal(tt, u) {
					t.Errorf("convertLean(%v, %v) steps, but Go does not convert", tt, u)
				}
			}
			if tt.Kind() == reflect.Interface {
				continue // never a dynamic type
			}
			x := reflect.Zero(tt).Interface()
			p, panicked := catch(func() { ConvertAt(x, reflect.Zero(reflect.PointerTo(u)).Interface()) })
			if panicked && !IsStuck(p) {
				t.Errorf("ConvertAt(%v, %v) panicked %v", tt, u, p)
			}
			if !panicked {
				nAt++
				if !goLegal(tt, u) {
					t.Errorf("ConvertAt(%v, %v) steps, but Go does not convert", tt, u)
				}
			}
		}
	}
	t.Logf("%d corpus types: %d pairs Go converts; a Lean Convert rule steps on %d, ConvertAt on %d, all of them Go's",
		len(es), nGo, nLean, nAt)
}
