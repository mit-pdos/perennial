package reflectcore

import (
	"reflect"
	"testing"
	"unsafe"
)

// leanKindOf is a copy of the Lean kindOf table (Perennial/Golang/Defn/Reflect.lean): the
// reflect.Kind number of each predeclared type and type constructor.
var leanKindOf = map[string]int{
	"bool": 1, "int": 2, "int8": 3, "int16": 4, "int32": 5, "int64": 6,
	"uint": 7, "uint8": 8, "uint16": 9, "uint32": 10, "uint64": 11, "uintptr": 12,
	"float32": 13, "float64": 14, "complex64": 15, "complex128": 16,
	"ArrayType": 17, "ChannelType": 18, "FunctionType": 19, "InterfaceType": 20, "MapType": 21,
	"PointerType": 22, "SliceType": 23, "string": 24, "StructType": 25, "unsafe.Pointer": 26,
}

// TypeQuery kind is the kindOf row of the type's underlying type, and reflect's Kind, for every
// predeclared type, every type constructor, named types of each, generic instances; through a
// token and through a pointer-any.
func TestTypeKind(t *testing.T) {
	x := 0
	cases := []struct {
		tok  any
		lean string // the kindOf row of the underlying type
	}{
		{tok[bool](), "bool"}, {tok[int](), "int"}, {tok[int8](), "int8"}, {tok[int16](), "int16"},
		{tok[int32](), "int32"}, {tok[rune](), "int32"}, {tok[int64](), "int64"},
		{tok[uint](), "uint"}, {tok[uint8](), "uint8"}, {tok[byte](), "uint8"},
		{tok[uint16](), "uint16"}, {tok[uint32](), "uint32"}, {tok[uint64](), "uint64"},
		{tok[uintptr](), "uintptr"}, {tok[float32](), "float32"}, {tok[float64](), "float64"},
		{tok[complex64](), "complex64"}, {tok[complex128](), "complex128"},
		{tok[string](), "string"}, {tok[unsafe.Pointer](), "unsafe.Pointer"},
		{tok[[3]int](), "ArrayType"}, {tok[[0]int](), "ArrayType"}, {tok[chan int](), "ChannelType"},
		{tok[<-chan int](), "ChannelType"}, {tok[func()](), "FunctionType"},
		{tok[any](), "InterfaceType"}, {tok[error](), "InterfaceType"},
		{tok[myIface](), "InterfaceType"}, {tok[map[int]int](), "MapType"},
		{tok[*int](), "PointerType"}, {tok[[]int](), "SliceType"}, {tok[struct{}](), "StructType"},
		{tok[S](), "StructType"}, {tok[myInt](), "int"}, {tok[myUint8](), "uint8"},
		{tok[myString](), "string"}, {tok[myBool](), "bool"}, {tok[myFloat](), "float64"},
		{tok[myPtr](), "PointerType"}, {tok[mySlice](), "SliceType"}, {tok[myMap](), "MapType"},
		{tok[myFunc](), "FunctionType"}, {tok[myChan](), "ChannelType"},
		{tok[myUnsafe](), "unsafe.Pointer"}, {tok[myArr](), "ArrayType"},
		{tok[G[int]](), "StructType"}, {tok[GSlice[int]](), "SliceType"},
		{tok[GPtr[int]](), "PointerType"}, {tok[**int](), "PointerType"},
		{&x, "int"}, {&S{}, "StructType"},
	}
	for _, c := range cases {
		want, ok := leanKindOf[c.lean]
		if !ok {
			t.Fatalf("no kindOf row %s", c.lean)
		}
		T := reflect.TypeOf(c.tok).Elem()
		if got := TypeKind(c.tok); got != want || int(T.Kind()) != want {
			t.Errorf("TypeKind(%v) = %d, kindOf %s = %d, reflect %d", T, got, c.lean, want, T.Kind())
		}
		if reflect.Kind(want).String() == "" {
			t.Errorf("no reflect.Kind %d", want)
		}
	}
	mustStuck(t, "TypeKind nil", func() { TypeKind(nil) })
	mustStuck(t, "TypeKind of a value", func() { TypeKind(3) })
	mustStuck(t, "TypeKind named-pointer token", func() { TypeKind(myPtr(nil)) })
}

type fn func(int, ...string) (bool, error)

// The other rows S0 has against reflect's answers, written as static tokens.
func TestTypeQueryRows(t *testing.T) {
	type row struct {
		q    TypeQ
		tok  any
		i    int
		want any // nil: stuck
	}
	rows := []row{
		{QElem, tok[*int](), 0, tok[int]()}, {QElem, tok[myPtr](), 0, tok[int]()},
		{QElem, tok[[]string](), 0, tok[string]()}, {QElem, tok[mySlice](), 0, tok[int]()},
		{QElem, tok[[3]S](), 0, tok[S]()}, {QElem, tok[myArr](), 0, tok[int]()},
		{QElem, tok[<-chan myInt](), 0, tok[myInt]()}, {QElem, tok[myMap](), 0, tok[int]()},
		{QElem, tok[map[string][]byte](), 0, tok[[]byte]()}, {QElem, tok[**S](), 0, tok[*S]()},
		{QElem, tok[GPtr[string]](), 0, tok[string]()},
		{QElem, tok[int](), 0, nil}, {QElem, tok[S](), 0, nil}, {QElem, tok[func()](), 0, nil},
		{QElem, tok[unsafe.Pointer](), 0, nil}, {QElem, tok[string](), 0, nil},
		{QElem, tok[any](), 0, nil},
		{QKey, tok[map[string]int](), 0, tok[string]()}, {QKey, tok[myMap](), 0, tok[string]()},
		{QKey, tok[map[Emb]bool](), 0, tok[Emb]()}, {QKey, tok[[]int](), 0, nil},
		{QLen, tok[[3]int](), 0, 3}, {QLen, tok[[0]int](), 0, 0}, {QLen, tok[[1]S](), 0, 1},
		{QLen, tok[myArr](), 0, 3}, {QLen, tok[[]int](), 0, nil},
		{QChanDir, tok[chan int](), 0, 3}, {QChanDir, tok[<-chan int](), 0, 1},
		{QChanDir, tok[chan<- int](), 0, 2}, {QChanDir, tok[myRecvChan](), 0, 1},
		{QChanDir, tok[int](), 0, nil},
		{QNumField, tok[S](), 0, 7}, {QNumField, tok[struct{}](), 0, 0},
		{QNumField, tok[G[int]](), 0, 1}, {QNumField, tok[*S](), 0, nil},
		{QFieldName, tok[S](), 0, "A"}, {QFieldName, tok[S](), 1, "b"}, {QFieldName, tok[S](), 2, "_"},
		{QFieldName, tok[S](), 3, "Emb"}, {QFieldName, tok[S](), 4, "EmbP"},
		{QFieldName, tok[S](), 7, nil}, {QFieldName, tok[S](), -1, nil},
		{QFieldType, tok[S](), 0, tok[int]()}, {QFieldType, tok[S](), 2, tok[int]()},
		{QFieldType, tok[S](), 3, tok[Emb]()}, {QFieldType, tok[S](), 4, tok[*EmbP]()},
		{QFieldType, tok[S](), 5, tok[[]int]()}, {QFieldType, tok[Pair[int, myInt]](), 1, tok[myInt]()},
		{QFieldType, tok[S](), 7, nil}, {QFieldType, tok[int](), 0, nil},
		{QFieldEmbedded, tok[S](), 0, false}, {QFieldEmbedded, tok[S](), 3, true},
		{QFieldEmbedded, tok[S](), 4, true}, {QFieldEmbedded, tok[S](), 2, false},
		{QFieldEmbedded, tok[S](), 9, nil},
		{QNumIn, tok[fn](), 0, 2}, {QNumIn, tok[func()](), 0, 0}, {QNumIn, tok[int](), 0, nil},
		{QInType, tok[fn](), 0, tok[int]()}, {QInType, tok[fn](), 1, tok[[]string]()},
		{QInType, tok[fn](), 2, nil},
		{QNumOut, tok[fn](), 0, 2}, {QNumOut, tok[myFunc](), 0, 1},
		{QOutType, tok[fn](), 1, tok[error]()}, {QOutType, tok[myFunc](), 0, tok[string]()},
		{QOutType, tok[fn](), 2, nil},
		{QVariadic, tok[fn](), 0, true}, {QVariadic, tok[myFunc](), 0, false},
		{QVariadic, tok[S](), 0, nil},
		{QNumTypeArgs, tok[G[int]](), 0, 1}, {QNumTypeArgs, tok[Pair[string, map[int]string]](), 0, 2},
		{QNumTypeArgs, tok[Pair[G[int], G[Pair[int, int]]]](), 0, 2}, {QNumTypeArgs, tok[S](), 0, 0},
		{QNumTypeArgs, tok[int](), 0, 0}, {QNumTypeArgs, tok[[]int](), 0, 0},
	}
	for _, r := range rows {
		T := reflect.TypeOf(r.tok).Elem()
		if r.want == nil {
			mustStuck(t, r.q.String()+" "+T.String(), func() { TypeQuery(r.q, r.tok, r.i) })
			continue
		}
		if got := TypeQuery(r.q, r.tok, r.i); got != r.want {
			t.Errorf("TypeQuery %v (%v, %d) = %#v, want %#v", r.q, T, r.i, got, r.want)
		}
	}
	// reflect's own answers, for the corpus
	for _, e := range corpus() {
		T := e.typ
		switch T.Kind() {
		case reflect.Pointer, reflect.Slice, reflect.Array, reflect.Chan, reflect.Map:
			if TypeElem(e.tok) != Token(T.Elem()) {
				t.Errorf("TypeElem(%v)", T)
			}
		}
		if T.Kind() == reflect.Array && TypeLen(e.tok) != T.Len() {
			t.Errorf("TypeLen(%v)", T)
		}
		if T.Kind() == reflect.Struct {
			if TypeNumField(e.tok) != T.NumField() {
				t.Errorf("TypeNumField(%v)", T)
			}
			for i := 0; i < T.NumField(); i++ {
				f := T.Field(i)
				if TypeFieldType(e.tok, i) != Token(f.Type) || TypeQuery(QFieldName, e.tok, i) != f.Name ||
					TypeQuery(QFieldEmbedded, e.tok, i) != f.Anonymous {
					t.Errorf("field %d of %v", i, T)
				}
			}
		}
		if TypeKind(e.tok) != int(T.Kind()) || TypeKind(e.addr()) != int(T.Kind()) {
			t.Errorf("TypeKind(%v)", T)
		}
	}
	for q := range NoneInS0 {
		mustStuck(t, q.String()+" (none in S0)", func() { TypeQuery(q, tok[S](), 0) })
	}
}

// TypeQuery underlying is the token of the underlying type, without the tags of a defined struct
// type's fields (Lean's underlying); identByName holds of the defined types without type arguments
// and the unnamed pointers to them, not of type literals (struct literals among them), error or
// generic instances.
func TestTypeUnderlyingIdentByName(t *testing.T) {
	type tagged struct {
		A int `json:"a"`
	}
	rows := []struct {
		tok   any
		under any // nil: not checked (reflect cannot build it)
		ident bool
	}{
		{tok[int](), tok[int](), true}, {tok[myInt](), tok[int](), true},
		{tok[*myInt](), tok[*myInt](), true}, {tok[**myInt](), tok[**myInt](), false},
		{tok[*int](), tok[*int](), true}, {tok[string](), tok[string](), true},
		{tok[myString](), tok[string](), true}, {tok[unsafe.Pointer](), tok[unsafe.Pointer](), true},
		{tok[myUnsafe](), tok[unsafe.Pointer](), true},
		{tok[myPtr](), tok[*int](), true}, {tok[PS1](), tok[*S](), true}, {tok[*PS1](), tok[*PS1](), true},
		{tok[mySlice](), tok[[]int](), true}, {tok[[]int](), tok[[]int](), false},
		{tok[myMap](), tok[map[string]int](), true}, {tok[map[string]int](), tok[map[string]int](), false},
		{tok[myArr](), tok[[3]int](), true}, {tok[myFunc](), tok[func(int) string](), true},
		{tok[fn](), tok[func(int, ...string) (bool, error)](), true},
		{tok[myChan](), tok[chan int](), true}, {tok[myRecvChan](), tok[<-chan int](), true},
		{tok[Emb](), tok[struct{ X int }](), true}, {tok[*Emb](), tok[*Emb](), true},
		{tok[Tagged](), tok[struct{ A int }](), true}, {tok[tagged](), tok[struct{ A int }](), true},
		{tok[struct {
			A int `json:"a"`
		}](), tok[struct {
			A int `json:"a"`
		}](), false},
		{tok[struct{ X, y int }](), tok[struct{ X, y int }](), false}, {tok[struct{}](), tok[struct{}](), false},
		{tok[*struct{ X int }](), tok[*struct{ X int }](), false},
		{tok[G[int]](), tok[struct{ V int }](), false}, {tok[*G[int]](), tok[*G[int]](), false},
		{tok[GSlice[int]](), tok[[]int](), false},
		{tok[any](), tok[any](), false}, {tok[error](), tok[error](), false},
		{tok[myIface](), nil, true}, {tok[myAny](), nil, true}, {tok[S](), nil, true},
		{tok[*myIface](), tok[*myIface](), true},
	}
	for _, r := range rows {
		T := reflect.TypeOf(r.tok).Elem()
		if r.under != nil {
			if got := TypeUnderlying(r.tok); got != r.under {
				t.Errorf("TypeUnderlying(%v) = %v, want %v", T, reflect.TypeOf(got).Elem(), reflect.TypeOf(r.under).Elem())
			}
			if got := TypeUnderlying(TypeUnderlying(r.tok)); got != r.under {
				t.Errorf("TypeUnderlying of the underlying type of %v", T)
			}
			U := reflect.TypeOf(r.under).Elem()
			if U.Kind() != T.Kind() || !T.ConvertibleTo(U) || !IdenticalUnderlying(T, U) {
				t.Errorf("TypeUnderlying(%v) = %v: not its underlying type", T, U)
			}
		}
		if got := TypeIdentByName(r.tok); got != r.ident {
			t.Errorf("TypeIdentByName(%v) = %v, want %v", T, got, r.ident)
		}
	}
	// reflect's answers, for the corpus: a defined type (and the unnamed pointer to one) has a
	// name and no type arguments; the underlying type is unnamed or predeclared
	defined := func(T reflect.Type) bool { return T.Name() != "" && T != errorType && NumTypeArgs(T) == 0 }
	for _, e := range corpus() {
		T := e.typ
		want := defined(T) || T.Kind() == reflect.Pointer && T.Name() == "" && defined(T.Elem())
		if TypeIdentByName(e.tok) != want {
			t.Errorf("TypeIdentByName(%v)", T)
		}
		if TypeIdentByName(PtrTok(e.tok)) != defined(T) {
			t.Errorf("TypeIdentByName(*%v)", T)
		}
		if p, ok := catch(func() { Underlying(T) }); ok {
			t.Logf("TypeUnderlying(%v): %v", T, p)
			continue
		}
		U := reflect.TypeOf(TypeUnderlying(e.tok)).Elem()
		if U.Kind() != T.Kind() || !IdenticalUnderlying(T, U) || U.Name() != "" && U.PkgPath() != "" && U != reflect.TypeFor[unsafe.Pointer]() {
			t.Errorf("TypeUnderlying(%v) = %v", T, U)
		}
	}
	mustStuck(t, "TypeUnderlying nil", func() { TypeUnderlying(nil) })
	mustStuck(t, "TypeIdentByName of a value", func() { TypeIdentByName(3) })
}
