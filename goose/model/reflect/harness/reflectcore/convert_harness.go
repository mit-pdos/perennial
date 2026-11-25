package reflectcore

import "reflect"

// convertLean is Convert t u (v) for v of type t, by the Lean Convert rules: the [under] rules
// on t's and u's underlying types (convert_underlying), and convert_same. Their families:
//   - identical underlying types (is_convert_underlying_same), where a defined struct type's
//     underlying type has no tags (goose writes it without them);
//   - integer to integer, uintptr included (convert_<int>_to_<int>);
//   - a byte to string (convert_byte_to_string): string(rune(c));
//   - a slice of bytes to string and back (convert_bytes_to_string, convert_string_to_bytes),
//     the element any type whose underlying type is byte;
//   - a pointer to unsafe.Pointer (convert_pointer_to_unsafe); unsafe.Pointer to *E for a plain
//     E, or nil to any *E (convert_unsafe_to_pointer, convert_unsafe_nil_to_pointer);
//     unsafe.Pointer to uintptr (convert_unsafe_to_uintptr, arbitrary in Lean: here gc's address);
//   - a channel to a channel of the same element type, any directions (convert_channel);
//   - a pointer to a pointer whose base types have identical underlying types
//     (convert_pointer_same_underlying).
//
// Floats, complex numbers, runes to and from strings, other integers to string and slices to
// arrays have no rule.
func convertLean(v reflect.Value, u reflect.Type) (reflect.Value, bool) {
	t := v.Type()
	fk, tk := t.Kind(), u.Kind()
	switch {
	case IdenticalUnderlying(t, u):
		return reinterpret(v, u), true
	case isInteger(fk) && isInteger(tk):
		return v.Convert(u), true
	case fk == reflect.Uint8 && tk == reflect.String:
		return reflect.ValueOf(string(rune(v.Uint()))).Convert(u), true
	case fk == reflect.Slice && t.Elem().Kind() == reflect.Uint8 && tk == reflect.String:
		return reflect.ValueOf(string(v.Bytes())).Convert(u), true
	case fk == reflect.String && tk == reflect.Slice && u.Elem().Kind() == reflect.Uint8:
		return reinterpret(reflect.ValueOf([]byte(v.String())), u), true
	case fk == reflect.Pointer && tk == reflect.UnsafePointer:
		return reinterpret(reflect.ValueOf(v.UnsafePointer()), u), true
	case fk == reflect.UnsafePointer && tk == reflect.Pointer:
		if v.IsNil() || IsPlain(u.Elem()) {
			return reinterpret(v, u), true
		}
	case fk == reflect.UnsafePointer && tk == reflect.Uintptr:
		return reflect.ValueOf(uintptr(v.UnsafePointer())).Convert(u), true
	case fk == reflect.Chan && tk == reflect.Chan && t.Elem() == u.Elem():
		return reinterpret(v, u), true
	case fk == reflect.Pointer && tk == reflect.Pointer && IdenticalUnderlying(t.Elem(), u.Elem()):
		return reinterpret(v, u), true
	}
	return reflect.Value{}, false
}

// reinterpret is v's memory read at type u, of the same layout.
func reinterpret(v reflect.Value, u reflect.Type) reflect.Value {
	p := reflect.New(v.Type())
	p.Elem().Set(v)
	return reflect.NewAt(u, p.UnsafePointer()).Elem()
}

func isInteger(k reflect.Kind) bool {
	return reflect.Int <= k && k <= reflect.Uintptr
}

// IdenticalUnderlying reports whether t and u have identical underlying types as Lean sees them:
// gc's identity, except that the top-level fields of a defined struct type have no tags.
func IdenticalUnderlying(t, u reflect.Type) bool {
	if t.Kind() != u.Kind() {
		return false
	}
	switch t.Kind() {
	case reflect.Pointer, reflect.Slice:
		return t.Elem() == u.Elem()
	case reflect.Array:
		return t.Len() == u.Len() && t.Elem() == u.Elem()
	case reflect.Map:
		return t.Key() == u.Key() && t.Elem() == u.Elem()
	case reflect.Chan:
		return t.ChanDir() == u.ChanDir() && t.Elem() == u.Elem()
	case reflect.Func:
		if t.NumIn() != u.NumIn() || t.NumOut() != u.NumOut() || t.IsVariadic() != u.IsVariadic() {
			return false
		}
		for i := 0; i < t.NumIn(); i++ {
			if t.In(i) != u.In(i) {
				return false
			}
		}
		for i := 0; i < t.NumOut(); i++ {
			if t.Out(i) != u.Out(i) {
				return false
			}
		}
		return true
	case reflect.Interface:
		if t.NumMethod() != u.NumMethod() {
			return false
		}
		for i := 0; i < t.NumMethod(); i++ {
			m, n := t.Method(i), u.Method(i)
			if m.Name != n.Name || m.PkgPath != n.PkgPath || m.Type != n.Type {
				return false
			}
		}
		return true
	case reflect.Struct:
		if t.NumField() != u.NumField() {
			return false
		}
		for i := 0; i < t.NumField(); i++ {
			f, g := t.Field(i), u.Field(i)
			if f.Name != g.Name || f.PkgPath != g.PkgPath || f.Type != g.Type ||
				f.Anonymous != g.Anonymous || leanTag(t, f) != leanTag(u, g) {
				return false
			}
		}
		return true
	}
	return true
}

func leanTag(s reflect.Type, f reflect.StructField) reflect.StructTag {
	if s.Name() != "" {
		return ""
	}
	return f.Tag
}

// IsPlain is IsPlain (Perennial/Golang/Defn/Plain.lean): an integer or float type, an array of at
// least one plain element, a non-empty struct of plain, non-blank fields with no padding.
func IsPlain(t reflect.Type) bool {
	switch k := t.Kind(); {
	case isInteger(k), k == reflect.Float32, k == reflect.Float64:
		return true
	case k == reflect.Array:
		return t.Len() >= 1 && IsPlain(t.Elem())
	case k == reflect.Struct:
		if t.NumField() == 0 {
			return false
		}
		var off uintptr
		for i := 0; i < t.NumField(); i++ {
			f := t.Field(i)
			if f.Name == "_" || f.Offset != off || !IsPlain(f.Type) {
				return false
			}
			off += f.Type.Size()
		}
		return off == t.Size()
	}
	return false
}

// GoConvertible is go.Convertible (Perennial/Golang/Defn/Reflect.lean), ConvertAt's premise: Go's
// conversion rules for a non-constant value, one case per constructor, over the types as Lean has
// them (IdenticalUnderlying for identical underlying types).
func GoConvertible(t, u reflect.Type) bool {
	tk, uk := t.Kind(), u.Kind()
	numeric := func(k reflect.Kind) bool { return isInteger(k) || k == reflect.Float32 || k == reflect.Float64 }
	isComplex := func(k reflect.Kind) bool { return k == reflect.Complex64 || k == reflect.Complex128 }
	byteOrRuneSlice := func(s reflect.Type) bool {
		return s.Kind() == reflect.Slice && (s.Elem().Kind() == reflect.Uint8 || s.Elem().Kind() == reflect.Int32)
	}
	switch {
	case uk == reflect.Interface && t.Implements(u): // implements
	case tk == reflect.Chan && uk == reflect.Chan && t.ChanDir() == reflect.BothDir &&
		t.Elem() == u.Elem() && (t.Name() == "" || u.Name() == ""): // chan
	case IdenticalUnderlying(t, u): // underlying
	case tk == reflect.Pointer && uk == reflect.Pointer && t.Name() == "" && u.Name() == "" &&
		IdenticalUnderlying(t.Elem(), u.Elem()): // pointer
	case numeric(tk) && numeric(uk): // numeric
	case isComplex(tk) && isComplex(uk): // complex
	case (isInteger(tk) || byteOrRuneSlice(t)) && uk == reflect.String: // toString
	case tk == reflect.String && byteOrRuneSlice(u): // fromString
	case tk == reflect.Slice && uk == reflect.Array && t.Elem() == u.Elem(): // sliceArray
	case tk == reflect.Slice && uk == reflect.Pointer && u.Elem().Kind() == reflect.Array &&
		t.Elem() == u.Elem().Elem(): // slicePtrArray
	case (tk == reflect.Pointer || tk == reflect.Uintptr) && uk == reflect.UnsafePointer: // toUnsafe
	case tk == reflect.UnsafePointer && (uk == reflect.Pointer || uk == reflect.Uintptr): // fromUnsafe
	default:
		return false
	}
	return true
}
