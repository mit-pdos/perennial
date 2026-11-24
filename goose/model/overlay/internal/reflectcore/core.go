// Package reflectcore is the reflection primitives of the Go models of
// reflect: a package that the overlay adds to the standard library
// (Perennial/Code/internal/reflectcore.toml, replaces = ["*"]), so that the
// models can state each operation that Go cannot express without unsafe as
// a visible call.
//
// A token is the Go value any((*T)(nil)) for a type T: comparing two tokens
// with == compares the types, and a token is a map key. A pointer-any is
// any((*T)(p)), the address p of a T, typed; every primitive that reads only
// a type accepts either.
//
// Each exported function is a primitive stub: its GooseLang model is in
// Perennial/TrustedCode/internal/reflectcore.lean (an existing operation of
// the semantics at a type read from an interface value's dynamic type, or a
// fact about a type), and the Go body here is a placeholder that panics.
// The generic helpers of helpers.go are translated: a stub instantiates one
// at the dynamic type of its argument.
package reflectcore

import "unsafe"

// TokOf is the token of x's dynamic type (x is not nil): tokOf at that type.
func TokOf(x any) any {
	panic("reflectcore: primitive stub")
}

// Box is a pointer-any to a new variable holding x's dynamic value (x is
// not nil): box at x's dynamic type.
func Box(x any) any {
	panic("reflectcore: primitive stub")
}

// Load is the value *p of a pointer-any p, boxed in any: load at p's
// element type.
func Load(p any) any {
	panic("reflectcore: primitive stub")
}

// Alloc is a pointer-any to a new zero variable of t's type (t a token or
// pointer-any): alloc at that type.
func Alloc(t any) any {
	panic("reflectcore: primitive stub")
}

// PtrTok is the token of *T for t a token (or pointer-any) of T: ptrTok
// at T.
func PtrTok(t any) any {
	panic("reflectcore: primitive stub")
}

// ConvertAt is the conversion U(x) of x's dynamic value to t's type U (t a
// token or pointer-any of U), boxed in any.
func ConvertAt(x, t any) any {
	panic("reflectcore: primitive stub")
}

// FieldRefAt is &(*p).f, a pointer-any to field i of the struct a
// pointer-any p points to.
func FieldRefAt(p any, i int) any {
	panic("reflectcore: primitive stub")
}

// ArraySliceAt is (*p)[:] for a pointer-any p to an array.
func ArraySliceAt(p any) any {
	panic("reflectcore: primitive stub")
}

// EqNilAt is x == nil at x's dynamic type, a pointer, slice, map, channel,
// function or unsafe.Pointer type.
func EqNilAt(x any) bool {
	panic("reflectcore: primitive stub")
}

// PointerOfAt is the address that x's dynamic value, a pointer, map,
// channel, slice or unsafe.Pointer, refers to.
func PointerOfAt(x any) unsafe.Pointer {
	panic("reflectcore: primitive stub")
}

// TypeKind is the reflect.Kind of t's type (t a token or pointer-any).
func TypeKind(t any) int {
	panic("reflectcore: primitive stub")
}

// TypeElem is the token of the element type of t's type: of a pointer,
// slice, array, channel or map type (its value type).
func TypeElem(t any) any {
	panic("reflectcore: primitive stub")
}

// TypeLen is the length of t's type, an array type.
func TypeLen(t any) int {
	panic("reflectcore: primitive stub")
}

// TypeNumField is the number of fields of t's type, a struct type.
func TypeNumField(t any) int {
	panic("reflectcore: primitive stub")
}

// TypeFieldType is the token of the type of field i of t's type, a struct
// type.
func TypeFieldType(t any, i int) any {
	panic("reflectcore: primitive stub")
}
