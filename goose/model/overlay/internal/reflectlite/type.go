// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package reflectlite implements lightweight version of reflect, not using
// any package except for "runtime", "unsafe", and "internal/abi"
//
// MODEL: a whole-package Go model (Perennial/Code/internal/reflectlite.toml),
// rewritten from the real files over the reflection primitives of
// internal/reflectcore, as the model of reflect is.
package reflectlite

import (
	"internal/abi"
	"internal/gomodel"
	"internal/reflectcore"
)

// Type is the representation of a Go type.
//
// Not all methods apply to all kinds of types. Restrictions,
// if any, are noted in the documentation for each method.
// Use the Kind method to find out the kind of type before
// calling kind-specific methods. Calling a method
// inappropriate to the kind of type causes a run-time panic.
//
// Type values are comparable, such as with the == operator,
// so they can be used as map keys.
// Two Type values are equal if they represent identical types.
//
// MODEL: the unexported methods common and uncommon are replaced by tok. An
// interface type is never a value's dynamic type, and only the package's own
// rtype implements Type in either; reflection does not observe an
// interface's methods (no numMethod row).
type Type interface {
	// Methods applicable to all types.

	// Name returns the type's name within its package for a defined type.
	// For other (non-defined) types it returns the empty string.
	Name() string

	// PkgPath returns a defined type's package path, that is, the import path
	// that uniquely identifies the package, such as "encoding/base64".
	// If the type was predeclared (string, error) or not defined (*T, struct{},
	// []int, or A where A is an alias for a non-defined type), the package path
	// will be the empty string.
	PkgPath() string

	// Size returns the number of bytes needed to store
	// a value of the given type; it is analogous to unsafe.Sizeof.
	Size() uintptr

	// Kind returns the specific kind of this type.
	Kind() Kind

	// Implements reports whether the type implements the interface type u.
	Implements(u Type) bool

	// AssignableTo reports whether a value of the type is assignable to type u.
	AssignableTo(u Type) bool

	// Comparable reports whether values of this type are comparable.
	Comparable() bool

	// String returns a string representation of the type.
	// The string representation may use shortened package names
	// (e.g., base64 instead of "encoding/base64") and is not
	// guaranteed to be unique among types. To test for type identity,
	// compare the Types directly.
	String() string

	// Elem returns a type's element type.
	// It panics if the type's Kind is not Ptr.
	Elem() Type

	tok() any
}

/*
 * These data structures are known to the compiler (../../cmd/internal/reflectdata/reflect.go).
 * A few are known to ../runtime/type.go to convey to debuggers.
 * They are also known to ../runtime/type.go.
 */

// A Kind represents the specific kind of type that a Type represents.
// The zero Kind is not a valid kind.
type Kind = abi.Kind

const Ptr = abi.Pointer

const (
	// Import-and-export these constants as necessary
	Interface = abi.Interface
	Slice     = abi.Slice
	String    = abi.String
	Struct    = abi.Struct
)

// MODEL: t is the type's token (internal/reflectcore); the methods have value
// receivers, so that == on Types compares the tokens, that is, the types.
type rtype struct {
	t any
}

func (t rtype) tok() any {
	return t.t
}

func (t rtype) Kind() Kind { return Kind(reflectcore.TypeKind(t.t)) }

// MODEL: names-only. Real's is abi.Type's, promoted through the embedded
// *abi.Type (as Kind is); the model's rtype has none of abi.Type's other
// methods.
func (t rtype) Size() uintptr {
	gomodel.Stuck()
	panic("unreachable")
}

func toRType(t any) rtype {
	return rtype{t}
}

// MODEL: the element type of an array, channel, map, pointer or slice type
// (abi.Type.Elem), else real's panic.
func elem(t any) any {
	switch Kind(reflectcore.TypeKind(t)) {
	case abi.Array, abi.Chan, abi.Map, abi.Pointer, abi.Slice:
		return reflectcore.TypeElem(t)
	}
	panic("reflect: Elem of invalid type " + toRType(t).String())
}

func (t rtype) Elem() Type {
	return toType(elem(t.t))
}

// TypeOf returns the reflection Type that represents the dynamic type of i.
// If i is a nil interface value, TypeOf returns nil.
func TypeOf(i any) Type {
	if i == nil {
		return nil
	}
	// MODEL: real's Type values are *rtype, the model's rtype values; the
	// model's rtype (and reflect's) is go.layoutModelled, so reflection on it
	// is stuck.
	return toRType(reflectcore.TokOf(i))
}

func (t rtype) Implements(u Type) bool {
	if u == nil {
		panic("reflect: nil type passed to Type.Implements")
	}
	if u.Kind() != Interface {
		panic("reflect: non-interface type passed to Type.Implements")
	}
	return implements(u.tok(), t.t)
}

func (t rtype) AssignableTo(u Type) bool {
	if u == nil {
		panic("reflect: nil type passed to Type.AssignableTo")
	}
	uu := u.tok()
	tt := t.t
	return directlyAssignable(uu, tt) || implements(uu, tt)
}

// implements reports whether the type V implements the interface type T.
//
// MODEL: for a V that is not an interface type, whether the type assertion
// of a value of type V (a zero one) to T succeeds, which compares V's method
// set with T's as real's merge walk over the two method tables does. An
// interface V is not modelled.
func implements(T, V any) bool {
	if Kind(reflectcore.TypeKind(T)) != abi.Interface {
		return false
	}
	if Kind(reflectcore.TypeKind(V)) == abi.Interface {
		gomodel.Stuck()
	}
	return reflectcore.AssertOk(T, reflectcore.Load(reflectcore.Alloc(V)))
}

// directlyAssignable reports whether a value x of type V can be directly
// assigned (using memmove) to a value of type T.
// https://golang.org/doc/go_spec.html#Assignability
// Ignoring the interface rules (implemented elsewhere)
// and the ideal constant rules (no ideal constants at run time).
//
// MODEL: decided only where tokens decide it. Equal tokens are the same type
// for a defined type without type arguments or a pointer to one
// (TypeIdentByName); for another type they are not modelled. Two different
// defined types are not assignable. For the other types of a kind, an
// underlying type that differs (TypeUnderlying) is not identical: real
// compares the parts of the types, which differ; except for the kinds where
// real's haveIdenticalUnderlyingType is not type identity (Chan: a
// bidirectional channel type; Func: it ignores IsVariadic), or the
// underlying type is not Go's (Struct: a defined struct type's has no field
// tags), and Interface, which are not modelled. Equal underlying types are
// not modelled.
func directlyAssignable(T, V any) bool {
	// x's type V is identical to T?
	if T == V {
		if reflectcore.TypeIdentByName(T) {
			return true
		}
		gomodel.Stuck()
	}

	// Otherwise at least one of T and V must not be defined
	// and they must have the same kind.
	kind := Kind(reflectcore.TypeKind(T))
	if isDefined(T) && isDefined(V) || kind != Kind(reflectcore.TypeKind(V)) {
		return false
	}

	// x's type T and V must  have identical underlying types.
	switch kind {
	case abi.Chan, abi.Func, abi.Interface, abi.Struct:
		gomodel.Stuck()
	}
	if reflectcore.TypeUnderlying(T) != reflectcore.TypeUnderlying(V) {
		return false
	}
	gomodel.Stuck()
	panic("unreachable")
}

// MODEL: whether t's type is a defined type without type arguments: one
// that TypeIdentByName holds of and that is not the unnamed pointer type to
// its element type.
func isDefined(t any) bool {
	if !reflectcore.TypeIdentByName(t) {
		return false
	}
	return Kind(reflectcore.TypeKind(t)) != abi.Pointer || t != reflectcore.PtrTok(reflectcore.TypeElem(t))
}

// toType converts from a *rtype to a Type that can be returned
// to the client of package reflect. In gc, the only concern is that
// a nil *rtype must be replaced by a nil Type, but in gccgo this
// function takes care of ensuring that multiple *rtype for the same
// type are coalesced into a single Type.
func toType(t any) Type {
	if t == nil {
		return nil
	}
	return toRType(t)
}

// MODEL: whether an interface holding a value of t's type stores the value
// in its data word (abi.Type.IsDirectIface): gc's types.IsDirectIface, a type
// of one pointer word (size and pointer-data size PtrSize). That is a pointer,
// channel, map, function or unsafe.Pointer type; an array of one element of
// such a type; or a struct whose last field has such a type and whose other
// fields are zero-size (a zero-size last field pads the struct). No type of
// the model is not-in-heap. (reflect's model has the same function.)
func isDirectIface(t any) bool {
	switch Kind(reflectcore.TypeKind(t)) {
	case abi.Pointer, abi.Chan, abi.Map, abi.Func, abi.UnsafePointer:
		return true
	case abi.Array:
		return reflectcore.TypeLen(t) == 1 && isDirectIface(reflectcore.TypeElem(t))
	case abi.Struct:
		n := reflectcore.TypeNumField(t)
		if n == 0 || !isDirectIface(reflectcore.TypeFieldType(t, n-1)) {
			return false
		}
		for i := 0; i < n-1; i++ {
			if !isZeroSize(reflectcore.TypeFieldType(t, i)) {
				return false
			}
		}
		return true
	}
	return false
}

// MODEL: whether t's type has size zero: an array of length zero or of a
// zero-size element, or a struct of zero-size fields.
func isZeroSize(t any) bool {
	switch Kind(reflectcore.TypeKind(t)) {
	case abi.Array:
		return reflectcore.TypeLen(t) == 0 || isZeroSize(reflectcore.TypeElem(t))
	case abi.Struct:
		for i := 0; i < reflectcore.TypeNumField(t); i++ {
			if !isZeroSize(reflectcore.TypeFieldType(t, i)) {
				return false
			}
		}
		return true
	}
	return false
}
