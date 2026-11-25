// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package reflectlite

import (
	"internal/abi"
	"internal/gomodel"
	"internal/reflectcore"
)

// Value is the reflection interface to a Go value.
//
// Not all methods apply to all kinds of values. Restrictions,
// if any, are noted in the documentation for each method.
// Use the Kind method to find out the kind of value before
// calling kind-specific methods. Calling a method
// inappropriate to the kind of type causes a run time panic.
//
// The zero Value represents no value.
// Its IsValid method returns false, its Kind method returns Invalid,
// its String method returns "<invalid Value>", and all other methods panic.
// Most functions and methods never return an invalid value.
// If one does, its documentation states the conditions explicitly.
//
// A Value can be used concurrently by multiple goroutines provided that
// the underlying Go value can be used concurrently for the equivalent
// direct operations.
//
// To compare two Values, compare the results of the Interface method.
// Using == on two Values does not compare the underlying values
// they represent.
type Value struct {
	// typ_ holds the type of the value represented by a Value.
	// Access using the typ method to avoid escape of v.
	//
	// MODEL: the type's token (internal/reflectcore); nil for the zero Value.
	typ_ any

	// Pointer-valued data or, if flagIndir is set, pointer to data.
	// Valid when either flagIndir is set or typ.pointers() is true.
	//
	// MODEL: if flagIndir is set, a pointer-any *T to the data (of type T);
	// else the data itself, a T (only for a type T that isDirectIface).
	ptr any

	// flag holds metadata about the value.
	//
	// The lowest five bits give the Kind of the value, mirroring typ.Kind().
	//
	// The next set of bits are flag bits:
	//	- flagStickyRO: obtained via unexported not embedded field, so read-only
	//	- flagEmbedRO: obtained via unexported embedded field, so read-only
	//	- flagIndir: val holds a pointer to the data
	//	- flagAddr: v.CanAddr is true (implies flagIndir and ptr is non-nil)
	//	- flagMethod: v is a method value.
	// If !typ.IsDirectIface(), code can assume that flagIndir is set.
	//
	// The remaining 22+ bits give a method number for method values.
	// If flag.kind() != Func, code can assume that flagMethod is unset.
	flag

	// A method value represents a curried method invocation
	// like r.Read for some receiver r. The typ+val+flag bits describe
	// the receiver r, but the flag's Kind bits say Func (methods are
	// functions), and the top bits of the flag give the method number
	// in r's type's method table.
}

type flag uintptr

const (
	flagKindWidth        = 5 // there are 27 kinds
	flagKindMask    flag = 1<<flagKindWidth - 1
	flagStickyRO    flag = 1 << 5
	flagEmbedRO     flag = 1 << 6
	flagIndir       flag = 1 << 7
	flagAddr        flag = 1 << 8
	flagMethod      flag = 1 << 9
	flagMethodShift      = 10
	flagRO          flag = flagStickyRO | flagEmbedRO
)

func (f flag) kind() Kind {
	return Kind(f & flagKindMask)
}

func (f flag) ro() flag {
	if f&flagRO != 0 {
		return flagStickyRO
	}
	return 0
}

// MODEL: the token typ_.
func (v Value) typ() any {
	return v.typ_
}

// packEface converts v to the empty interface.
//
// MODEL: the whole interface (a GooseLang interface value holds the data, not
// a data word); Load copies the data out, as real copies an addressable value.
func packEface(v Value) any {
	t := v.typ()
	switch {
	case !isDirectIface(t):
		if v.flag&flagIndir == 0 {
			panic("bad indir")
		}
		// Value is indirect, and so is the interface we're making.
		return reflectcore.Load(v.ptr)
	case v.flag&flagIndir != 0:
		// Value is indirect, but interface is direct. We need
		// to load the data at v.ptr into the interface data word.
		return reflectcore.Load(v.ptr)
	default:
		// Value is direct, and so is the interface.
		return v.ptr
	}
}

// unpackEface converts the empty interface i to a Value.
//
// MODEL: an indirect value is boxed (a new variable holding i's value).
func unpackEface(i any) Value {
	if i == nil {
		return Value{}
	}
	t := reflectcore.TokOf(i)
	f := flag(reflectcore.TypeKind(t))
	if !isDirectIface(t) {
		f |= flagIndir
		return Value{t, reflectcore.Box(i), f}
	}
	return Value{t, i, f}
}

// A ValueError occurs when a Value method is invoked on
// a Value that does not support it. Such cases are documented
// in the description of each method.
type ValueError struct {
	Method string
	Kind   Kind
}

func (e *ValueError) Error() string {
	if e.Kind == 0 {
		return "reflect: call of " + e.Method + " on zero Value"
	}
	return "reflect: call of " + e.Method + " on " + e.Kind.String() + " Value"
}

// methodName returns the name of the calling method,
// assumed to be two stack frames above.
//
// MODEL: names-only. Real's body walks the stack with runtime.Caller.
func methodName() string {
	gomodel.Stuck()
	panic("unreachable")
}

// mustBeExported panics if f records that the value was obtained using
// an unexported field.
func (f flag) mustBeExported() {
	if f == 0 {
		panic(&ValueError{methodName(), 0})
	}
	if f&flagRO != 0 {
		panic("reflect: " + methodName() + " using value obtained using unexported field")
	}
}

// mustBeAssignable panics if f records that the value is not assignable,
// which is to say that either it was obtained using an unexported field
// or it is not addressable.
func (f flag) mustBeAssignable() {
	if f == 0 {
		panic(&ValueError{methodName(), abi.Invalid})
	}
	// Assignable if addressable and not read-only.
	if f&flagRO != 0 {
		panic("reflect: " + methodName() + " using value obtained using unexported field")
	}
	if f&flagAddr == 0 {
		panic("reflect: " + methodName() + " using unaddressable value")
	}
}

// CanSet reports whether the value of v can be changed.
// A Value can be changed only if it is addressable and was not
// obtained by the use of unexported struct fields.
// If CanSet returns false, calling Set or any type-specific
// setter (e.g., SetBool, SetInt) will panic.
func (v Value) CanSet() bool {
	return v.flag&(flagAddr|flagRO) == flagAddr
}

// Elem returns the value that the interface v contains
// or that the pointer v points to.
// It panics if v's Kind is not Interface or Pointer.
// It returns the zero Value if v is nil.
func (v Value) Elem() Value {
	k := v.kind()
	switch k {
	case abi.Interface:
		// MODEL: the interface value *v.ptr, converted to any (for both
		// layouts).
		eface := reflectcore.Load(v.ptr)
		x := unpackEface(eface)
		if x.flag != 0 {
			x.flag |= v.flag.ro()
		}
		return x
	case abi.Pointer:
		ptr := v.ptr
		if v.flag&flagIndir != 0 {
			ptr = reflectcore.Load(ptr)
		}
		// The returned value's address is v's value.
		if reflectcore.EqNilAt(ptr) {
			return Value{}
		}
		typ := reflectcore.TypeElem(v.typ())
		fl := v.flag&flagRO | flagIndir | flagAddr
		fl |= flag(reflectcore.TypeKind(typ))
		return Value{typ, reflectcore.ConvertAt(ptr, reflectcore.PtrTok(typ)), fl}
	}
	panic(&ValueError{"reflectlite.Value.Elem", v.kind()})
}

func valueInterface(v Value) any {
	if v.flag == 0 {
		panic(&ValueError{"reflectlite.Value.Interface", 0})
	}

	if v.kind() == abi.Interface {
		// Special case: return the element inside the interface.
		//
		// MODEL: the interface value *v.ptr, converted to any (for both
		// layouts).
		return reflectcore.Load(v.ptr)
	}

	return packEface(v)
}

// IsNil reports whether its argument v is nil. The argument must be
// a chan, func, interface, map, pointer, or slice value; if it is
// not, IsNil panics. Note that IsNil is not always equivalent to a
// regular comparison with nil in Go. For example, if v was created
// by calling ValueOf with an uninitialized interface variable i,
// i==nil will be true but v.IsNil will panic as v will be the zero
// Value.
func (v Value) IsNil() bool {
	k := v.kind()
	switch k {
	case abi.Chan, abi.Func, abi.Map, abi.Pointer, abi.UnsafePointer:
		// if v.flag&flagMethod != 0 {
		// 	return false
		// }
		ptr := v.ptr
		if v.flag&flagIndir != 0 {
			ptr = reflectcore.Load(ptr)
		}
		return reflectcore.EqNilAt(ptr)
	case abi.Interface:
		// Interface is always bigger than a word; assume flagIndir.
		return reflectcore.Load(v.ptr) == nil
	case abi.Slice:
		// Slice is always bigger than a word; assume flagIndir.
		return reflectcore.EqNilAt(reflectcore.Load(v.ptr))
	}
	panic(&ValueError{"reflectlite.Value.IsNil", v.kind()})
}

// IsValid reports whether v represents a value.
// It returns false if v is the zero Value.
// If IsValid returns false, all other methods except String panic.
// Most functions and methods never return an invalid Value.
// If one does, its documentation states the conditions explicitly.
func (v Value) IsValid() bool {
	return v.flag != 0
}

// Kind returns v's Kind.
// If v is the zero Value (IsValid returns false), Kind returns Invalid.
func (v Value) Kind() Kind {
	return v.kind()
}

// Set assigns x to the value v.
// It panics if CanSet returns false.
// As in Go, x's value must be assignable to v's type.
//
// MODEL: typedmemmove and the store of the data word are Store.
func (v Value) Set(x Value) {
	v.mustBeAssignable()
	x.mustBeExported() // do not let unexported x leak
	var target any
	if v.kind() == abi.Interface {
		target = v.ptr
	}
	x = x.assignTo("reflectlite.Set", v.typ(), target)
	if x.flag&flagIndir != 0 {
		reflectcore.Store(v.ptr, reflectcore.Load(x.ptr))
	} else {
		reflectcore.Store(v.ptr, x.ptr)
	}
}

// Type returns v's type.
func (v Value) Type() Type {
	f := v.flag
	if f == 0 {
		panic(&ValueError{"reflectlite.Value.Type", abi.Invalid})
	}
	// Method values not supported.
	return toRType(v.typ())
}

/*
 * constructors
 */

// ValueOf returns a new Value initialized to the concrete value
// stored in the interface i. ValueOf(nil) returns the zero Value.
func ValueOf(i any) Value {
	if i == nil {
		return Value{}
	}
	return unpackEface(i)
}

// assignTo returns a value v that can be assigned directly to typ.
// It panics if v is not assignable to typ.
// For a conversion to an interface type, target is a suggested scratch space to use.
//
// MODEL: target is a pointer-any to a dst, or nil; unsafe_New is Alloc, the
// conversion to dst stored into *target (ifaceE2I) is Store.
func (v Value) assignTo(context string, dst any, target any) Value {
	// if v.flag&flagMethod != 0 {
	// 	v = makeMethodValue(context, v)
	// }

	switch {
	case directlyAssignable(dst, v.typ()):
		// Overwrite type so that they match.
		// Same memory layout, so no harm done.
		fl := v.flag&(flagAddr|flagIndir) | v.flag.ro()
		fl |= flag(reflectcore.TypeKind(dst))
		return Value{dst, v.ptr, fl}

	case implements(dst, v.typ()):
		if target == nil {
			target = reflectcore.Alloc(dst)
		}
		if v.Kind() == abi.Interface && v.IsNil() {
			// A nil ReadWriter passed to nil Reader is OK,
			// but using ifaceE2I below will panic.
			// Avoid the panic by returning a nil dst (e.g., Reader) explicitly.
			return Value{dst, nil, flag(abi.Interface)}
		}
		x := valueInterface(v)
		reflectcore.Store(target, x)
		return Value{dst, target, flagIndir | flag(abi.Interface)}
	}

	// Failed.
	panic(context + ": value of type " + toRType(v.typ()).String() + " is not assignable to type " + toRType(dst).String())
}
