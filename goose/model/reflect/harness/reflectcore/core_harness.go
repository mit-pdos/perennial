// Package reflectcore is the harness's internal/reflectcore: each primitive stub of
// goose/model/overlay/internal/reflectcore/core.go written in Go over the real reflect and
// unsafe. A stub steps where its GooseLang rule (Perennial/Golang/Defn/Reflect.lean) steps, with
// the rule's result, and panics "stuck: ..." where the rule has no step. helpers.go, the
// translated generic helpers, is copied from the overlay by ../gen.sh. Test-only.
//
// A token of a Go type T is the Go value any((*T)(nil)); a pointer-any is any(p) for a p of the
// unnamed type *T.
package reflectcore

import (
	"fmt"
	"reflect"
	"strings"
	"unsafe"
)

func stuck(format string, args ...any) {
	panic("stuck: " + fmt.Sprintf(format, args...))
}

// IsStuck reports whether a recovered panic value is a stuck point of the harness: of a stub
// here, or the harness gomodel.Stuck.
func IsStuck(p any) bool {
	s, ok := p.(string)
	return ok && strings.HasPrefix(s, "stuck")
}

// Token is the token of t, any((*t)(nil)).
func Token(t reflect.Type) any {
	return reflect.Zero(reflect.PointerTo(t)).Interface()
}

// Shape is go.Shape (Perennial/GooseLang/Lang.lean).
type Shape struct {
	Kind  ShapeKind
	Dir   reflect.ChanDir // for ShapeChan
	Inner *Shape          // for ShapeDeref
}

type ShapeKind int

const (
	ShapeSelf ShapeKind = iota
	ShapeSlice
	ShapeMap
	ShapePtr
	ShapeChan
	ShapeDeref
)

var (
	Self      = Shape{Kind: ShapeSelf}
	DerefSelf = Shape{Kind: ShapeDeref, Inner: &Self}
)

// ShapeArgs is shapeArgs: the type arguments a dispatch argument of dynamic type d gives, or
// false.
func ShapeArgs(s Shape, d reflect.Type) ([]reflect.Type, bool) {
	switch s.Kind {
	case ShapeSelf:
		return []reflect.Type{d}, true
	case ShapeSlice:
		if d.Kind() == reflect.Slice {
			return []reflect.Type{d, d.Elem()}, true
		}
	case ShapeMap:
		if d.Kind() == reflect.Map {
			return []reflect.Type{d, d.Key(), d.Elem()}, true
		}
	case ShapePtr:
		if d.Kind() == reflect.Pointer {
			return []reflect.Type{d, d.Elem()}, true
		}
	case ShapeChan:
		if d.Kind() == reflect.Chan && d.ChanDir() == s.Dir {
			return []reflect.Type{d, d.Elem()}, true
		}
	case ShapeDeref:
		// d is, syntactically, the unnamed *t
		if d.Kind() == reflect.Pointer && d.Name() == "" {
			return ShapeArgs(*s.Inner, d.Elem())
		}
	}
	return nil, false
}

// FuncResolveAt is the type-argument list of FuncResolveAt shs f on the dispatch interfaces is:
// stuck on a nil interface or a dynamic type that does not fit its shape.
func FuncResolveAt(shs []Shape, f string, is ...any) []reflect.Type {
	if len(is) != len(shs) {
		stuck("FuncResolveAt %s: %d dispatch arguments for %d shapes", f, len(is), len(shs))
	}
	var ts []reflect.Type
	for k, i := range is {
		if i == nil {
			stuck("FuncResolveAt %s: dispatch argument %d is the nil interface", f, k)
		}
		args, ok := ShapeArgs(shs[k], reflect.TypeOf(i))
		if !ok {
			stuck("FuncResolveAt %s: dynamic type %v does not fit shape %d", f, reflect.TypeOf(i), k)
		}
		ts = append(ts, args...)
	}
	return ts
}

var nilPtr *int

// nilDeref is Go's nil dereference.
func nilDeref() int {
	return *nilPtr
}

// TokOf is FuncResolveAt [self] tokOf: tokOf[T](x) for x's dynamic type T.
func TokOf(x any) any {
	t := FuncResolveAt([]Shape{Self}, "tokOf", x)[0]
	return Token(t)
}

// Box is FuncResolveAt [self] box: box[T](x) = q := new(T); *q = x.(T); return q.
func Box(x any) any {
	t := FuncResolveAt([]Shape{Self}, "box", x)[0]
	q := reflect.New(t)
	q.Elem().Set(reflect.ValueOf(x))
	return q.Interface()
}

// Load is FuncResolveAt [deref self] load: load[T](p) = *p.(*T) for p's dynamic type *T.
func Load(p any) any {
	FuncResolveAt([]Shape{DerefSelf}, "load", p)
	v := reflect.ValueOf(p)
	if v.IsNil() {
		nilDeref()
	}
	return v.Elem().Interface()
}

// Alloc is FuncResolveAt [deref self] alloc: alloc[T](t) = new(T) for t's dynamic type *T.
func Alloc(t any) any {
	e := FuncResolveAt([]Shape{DerefSelf}, "alloc", t)[0]
	return reflect.New(e).Interface()
}

// PtrTok is FuncResolveAt [deref self] ptrTok: ptrTok[T](t) = (**T)(nil) for t's dynamic type *T.
func PtrTok(t any) any {
	e := FuncResolveAt([]Shape{DerefSelf}, "ptrTok", t)[0]
	return Token(reflect.PointerTo(e))
}

// assertible is whether the type assertion x.(T) succeeds.
func assertible(x any, T reflect.Type) bool {
	if x == nil {
		return false
	}
	if T.Kind() == reflect.Interface {
		return reflect.TypeOf(x).Implements(T)
	}
	return reflect.TypeOf(x) == T
}

// Store is FuncResolveAt [deref self] store: store[T](p, x) = *p.(*T) = zero T for a nil x, else
// *p.(*T) = x.(T), for p's dynamic type *T.
func Store(p, x any) {
	e := FuncResolveAt([]Shape{DerefSelf}, "store", p)[0]
	pv := reflect.ValueOf(p)
	if x != nil && !assertible(x, e) {
		panic(fmt.Sprintf("interface conversion: interface {} is %v, not %v", reflect.TypeOf(x), e))
	}
	if pv.IsNil() {
		nilDeref()
	}
	if x == nil {
		pv.Elem().SetZero()
		return
	}
	pv.Elem().Set(reflect.ValueOf(x))
}

// AssertOk is FuncResolveAt [deref self] assertOk: assertOk[T](x) = _, ok := x.(T); ok for t's
// dynamic type *T.
func AssertOk(t, x any) bool {
	e := FuncResolveAt([]Shape{DerefSelf}, "assertOk", t)[0]
	return assertible(x, e)
}

// target is U for a token or pointer-any of dynamic type the unnamed *U; stuck otherwise.
func target(t any, what string) reflect.Type {
	if t == nil {
		stuck("%s: the type argument is the nil interface", what)
	}
	d := reflect.TypeOf(t)
	if d.Kind() != reflect.Pointer || d.Name() != "" {
		stuck("%s: the type argument's dynamic type %v is not an unnamed pointer type", what, d)
	}
	return d.Elem()
}

// ConvertAt is ConvertAt: any(U(x)) for x's dynamic type T and a token of U. For an interface U,
// x itself if T implements U; otherwise the conversion of the Lean Convert rules (convertLean).
// Stuck: x nil, a layout a model changes, an interface U that T does not implement, no Convert
// rule.
func ConvertAt(x, t any) any {
	if x == nil {
		stuck("ConvertAt: x is the nil interface")
	}
	u := target(t, "ConvertAt")
	from := reflect.TypeOf(x)
	if ConvertExposed(from) || ConvertExposed(u) {
		stuck("ConvertAt: from %v to %v: a layout a model changes", from, u)
	}
	if u.Kind() == reflect.Interface {
		if from.Implements(u) {
			return x
		}
		stuck("ConvertAt: %v does not implement %v", from, u)
	}
	v, ok := convertLean(reflect.ValueOf(x), u)
	if !ok {
		stuck("ConvertAt: no Convert rule from %v to %v", from, u)
	}
	return v.Interface()
}

// FieldRefAt is FieldRefAt: any(&(*p).f) for the i-th field f of p's struct type, p of dynamic
// type the unnamed *S. Stuck: S not a struct, p nil, i out of range, f blank.
func FieldRefAt(p any, i int) any {
	s := target(p, "FieldRefAt")
	if s.Kind() != reflect.Struct {
		stuck("FieldRefAt: %v is not a struct type", s)
	}
	if LayoutModelled(s) {
		stuck("FieldRefAt: %v is layoutModelled", s)
	}
	pv := reflect.ValueOf(p)
	if pv.IsNil() {
		stuck("FieldRefAt: nil pointer")
	}
	if i < 0 || i >= s.NumField() {
		stuck("FieldRefAt: field %d of %v", i, s)
	}
	f := s.Field(i)
	if f.Name == "_" {
		stuck("FieldRefAt: blank field %d of %v", i, s)
	}
	return reflect.NewAt(f.Type, unsafe.Add(pv.UnsafePointer(), f.Offset)).Interface()
}

// ArraySliceAt is ArraySliceAt: any((*p)[:]) for p of dynamic type the unnamed *[n]E. Stuck: not
// an array, p nil.
func ArraySliceAt(p any) any {
	a := target(p, "ArraySliceAt")
	if a.Kind() != reflect.Array {
		stuck("ArraySliceAt: %v is not an array type", a)
	}
	if LayoutModelled(a) {
		stuck("ArraySliceAt: %v is layoutModelled", a)
	}
	pv := reflect.ValueOf(p)
	if pv.IsNil() {
		stuck("ArraySliceAt: nil pointer")
	}
	return pv.Elem().Slice(0, a.Len()).Interface()
}

func nilable(k reflect.Kind) bool {
	switch k {
	case reflect.Pointer, reflect.Slice, reflect.Map, reflect.Chan, reflect.Func, reflect.UnsafePointer:
		return true
	}
	return false
}

// EqNilAt is EqNilAt: x == nil at x's dynamic type, for a pointer, slice, map, chan, func or
// unsafe.Pointer underlying type. Stuck: x nil, any other kind.
func EqNilAt(x any) bool {
	if x == nil {
		stuck("EqNilAt: x is the nil interface")
	}
	if !nilable(reflect.TypeOf(x).Kind()) {
		stuck("EqNilAt: no nil of %v", reflect.TypeOf(x))
	}
	if LayoutModelled(reflect.TypeOf(x)) {
		stuck("EqNilAt: %v is layoutModelled", reflect.TypeOf(x))
	}
	return reflect.ValueOf(x).IsNil()
}

// TypeQ is go.TypeQ (Perennial/GooseLang/Lang.lean), in its order.
type TypeQ int

const (
	QKind TypeQ = iota
	QName
	QNumTypeArgs
	QPkgName
	QElem
	QKey
	QLen
	QChanDir
	QNumField
	QFieldName
	QFieldType
	QFieldTag
	QFieldEmbedded
	QFieldPkg
	QNumIn
	QInType
	QNumOut
	QOutType
	QVariadic
	QNumMethod
	QMethodId
	QMethodType
	QUnderlying
	QIdentByName
)

var typeQNames = [...]string{"kind", "name", "numTypeArgs", "pkgName", "elem", "key", "len",
	"chanDir", "numField", "fieldName", "fieldType", "fieldTag", "fieldEmbedded", "fieldPkg",
	"numIn", "inType", "numOut", "outType", "variadic", "numMethod", "methodId", "methodType",
	"underlying", "identByName"}

func (q TypeQ) String() string { return typeQNames[q] }

// NoneInS0 are the TypeQuery rows whose typeQuery is none for every type in S0.
var NoneInS0 = map[TypeQ]bool{
	QName: true, QPkgName: true, QFieldTag: true, QFieldPkg: true,
	QNumMethod: true, QMethodId: true, QMethodType: true,
}

// ChanDirNum is the chanDir row's number of a direction: reflect.ChanDir's (RecvDir 1, SendDir 2,
// BothDir 3).
func ChanDirNum(d reflect.ChanDir) int { return int(d) }

// NumTypeArgs is the number of type arguments of a named type, from its name (G[A,B]).
func NumTypeArgs(t reflect.Type) int {
	name := t.Name()
	i := strings.IndexByte(name, '[')
	if i < 0 {
		return 0
	}
	n, depth := 1, 0
	for _, c := range name[i+1 : len(name)-1] {
		switch c {
		case '[', '(', '{':
			depth++
		case ']', ')', '}':
			depth--
		case ',':
			if depth == 0 {
				n++
			}
		}
	}
	return n
}

// TypeQuery is TypeQuery q on (t, i): the fact q about the type T of a token or pointer-any t.
// Stuck where typeQuery is none: a row of NoneInS0, a row other than identByName on a
// LayoutModelled type, a row that does not apply to T's kind, an index out of range.
func TypeQuery(q TypeQ, t any, i int) any {
	T := target(t, "TypeQuery "+q.String())
	if NoneInS0[q] {
		stuck("TypeQuery %v: none in S0", q)
	}
	if q != QIdentByName && LayoutModelled(T) {
		stuck("TypeQuery %v: %v is layoutModelled", q, T)
	}
	k := T.Kind()
	no := func() {
		stuck("TypeQuery %v: none for %v (index %d)", q, T, i)
	}
	switch q {
	case QKind:
		return int(k)
	case QNumTypeArgs:
		return NumTypeArgs(T)
	case QElem:
		switch k {
		case reflect.Pointer, reflect.Slice, reflect.Array, reflect.Chan, reflect.Map:
			return Token(T.Elem())
		}
	case QKey:
		if k == reflect.Map {
			return Token(T.Key())
		}
	case QLen:
		if k == reflect.Array {
			return T.Len()
		}
	case QChanDir:
		if k == reflect.Chan {
			return ChanDirNum(T.ChanDir())
		}
	case QNumField:
		if k == reflect.Struct {
			return T.NumField()
		}
	case QFieldName, QFieldType, QFieldEmbedded:
		if k == reflect.Struct && 0 <= i && i < T.NumField() {
			f := T.Field(i)
			switch q {
			case QFieldName:
				return f.Name
			case QFieldType:
				return Token(f.Type)
			default:
				return f.Anonymous
			}
		}
	case QNumIn:
		if k == reflect.Func {
			return T.NumIn()
		}
	case QInType:
		if k == reflect.Func && 0 <= i && i < T.NumIn() {
			return Token(T.In(i))
		}
	case QNumOut:
		if k == reflect.Func {
			return T.NumOut()
		}
	case QOutType:
		if k == reflect.Func && 0 <= i && i < T.NumOut() {
			return Token(T.Out(i))
		}
	case QVariadic:
		if k == reflect.Func {
			return T.IsVariadic()
		}
	case QUnderlying:
		return Token(Underlying(T))
	case QIdentByName:
		return IdentByName(T)
	}
	no()
	return nil
}

// TypeKind is TypeQuery kind.
func TypeKind(t any) int { return TypeQuery(QKind, t, 0).(int) }

// TypeElem is TypeQuery elem.
func TypeElem(t any) any { return TypeQuery(QElem, t, 0) }

// TypeLen is TypeQuery len.
func TypeLen(t any) int { return TypeQuery(QLen, t, 0).(int) }

// TypeNumField is TypeQuery numField.
func TypeNumField(t any) int { return TypeQuery(QNumField, t, 0).(int) }

// TypeFieldType is TypeQuery fieldType.
func TypeFieldType(t any, i int) any { return TypeQuery(QFieldType, t, i) }

// TypeUnderlying is TypeQuery underlying.
func TypeUnderlying(t any) any { return TypeQuery(QUnderlying, t, 0) }

// TypeIdentByName is TypeQuery identByName.
func TypeIdentByName(t any) bool { return TypeQuery(QIdentByName, t, 0).(bool) }

var errorType = reflect.TypeFor[error]()

// predeclared is the predeclared type of each basic kind.
var predeclared = map[reflect.Kind]reflect.Type{
	reflect.Bool: reflect.TypeFor[bool](), reflect.Int: reflect.TypeFor[int](),
	reflect.Int8: reflect.TypeFor[int8](), reflect.Int16: reflect.TypeFor[int16](),
	reflect.Int32: reflect.TypeFor[int32](), reflect.Int64: reflect.TypeFor[int64](),
	reflect.Uint: reflect.TypeFor[uint](), reflect.Uint8: reflect.TypeFor[uint8](),
	reflect.Uint16: reflect.TypeFor[uint16](), reflect.Uint32: reflect.TypeFor[uint32](),
	reflect.Uint64: reflect.TypeFor[uint64](), reflect.Uintptr: reflect.TypeFor[uintptr](),
	reflect.Float32: reflect.TypeFor[float32](), reflect.Float64: reflect.TypeFor[float64](),
	reflect.Complex64: reflect.TypeFor[complex64](), reflect.Complex128: reflect.TypeFor[complex128](),
	reflect.String: reflect.TypeFor[string](), reflect.UnsafePointer: reflect.TypeFor[unsafe.Pointer](),
}

// Underlying is the underlying type as Lean has it (underlying): Go's, except that the fields of a
// defined struct type's underlying type have no tags (goose's structType). It panics (not stuck)
// for a defined interface type and for a defined struct type with unexported fields, which reflect
// cannot construct.
func Underlying(T reflect.Type) reflect.Type {
	switch k := T.Kind(); k {
	case reflect.Pointer:
		return reflect.PointerTo(T.Elem())
	case reflect.Slice:
		return reflect.SliceOf(T.Elem())
	case reflect.Array:
		return reflect.ArrayOf(T.Len(), T.Elem())
	case reflect.Map:
		return reflect.MapOf(T.Key(), T.Elem())
	case reflect.Chan:
		return reflect.ChanOf(T.ChanDir(), T.Elem())
	case reflect.Func:
		var in, out []reflect.Type
		for i := 0; i < T.NumIn(); i++ {
			in = append(in, T.In(i))
		}
		for i := 0; i < T.NumOut(); i++ {
			out = append(out, T.Out(i))
		}
		return reflect.FuncOf(in, out, T.IsVariadic())
	case reflect.Interface:
		if T.Name() == "" || T == errorType {
			return T
		}
		panic("harness: the underlying type of a defined interface type")
	case reflect.Struct:
		if T.Name() == "" {
			return T
		}
		var fs []reflect.StructField
		for i := 0; i < T.NumField(); i++ {
			f := T.Field(i)
			if f.PkgPath != "" {
				panic("harness: the underlying type of a defined struct type with unexported fields")
			}
			fs = append(fs, reflect.StructField{Name: f.Name, Type: f.Type, Anonymous: f.Anonymous})
		}
		return reflect.StructOf(fs)
	default:
		return predeclared[k]
	}
}

// isDefined is whether T is a defined type without type arguments (Lean's go.Named n []): a
// named type other than error (an interface type literal in Lean) and a generic instance.
func isDefined(T reflect.Type) bool {
	return T.Name() != "" && T != errorType && !strings.Contains(T.Name(), "[")
}

// IdentByName is identByName (Perennial/Golang/Defn/Interface.lean): T is a defined type without
// type arguments or the unnamed pointer to one.
func IdentByName(T reflect.Type) bool {
	return isDefined(T) || T.Kind() == reflect.Pointer && T.Name() == "" && isDefined(T.Elem())
}
