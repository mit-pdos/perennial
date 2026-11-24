// The Go models of errors.Is and errors.As (Perennial/Code/errors.toml,
// [model]), spliced into wrap.go in place of the real declarations.

package errors

import "internal/reflectlite"

// MODEL: Is reports whether any error in err's tree matches target. Go's is
//
//	if err == nil || target == nil {
//		return err == target
//	}
//	isComparable := reflectlite.TypeOf(target).Comparable()
//	return is(err, target, isComparable)
//
// (is, which walks the error tree, is the real Go, translated). The model
// replaces the reflection call by true: the semantics cannot inspect the
// dynamic type of an interface value, so the model takes every target to be
// comparable. For a target whose dynamic type is not comparable (a slice
// type, say), Go's is skips err == target; the model performs it, and when
// some error of the tree has target's dynamic type that comparison is stuck
// (CheckComparable has no rule for an uncomparable type); comparing with an
// error of another dynamic type is false, as Go's skipped comparison would
// have been. The model is thus less defined than Go there, never different:
// wp_Is only admits nil and pointer targets. A semantics rule testing the
// comparability of an interface's dynamic type would let goose translate the
// real Is.
func Is(err, target error) bool {
	if err == nil || target == nil {
		return err == target
	}
	isComparable := true
	return is(err, target, isComparable)
}

// MODEL: As finds the first error in err's tree that matches target, and if
// one is found, sets target to that error value and returns true. Go's is
//
//	if err == nil {
//		return false
//	}
//	if target == nil {
//		panic("errors: target cannot be nil")
//	}
//	val := reflectlite.ValueOf(target)
//	typ := val.Type()
//	if typ.Kind() != reflectlite.Ptr || val.IsNil() {
//		panic("errors: target must be a non-nil pointer")
//	}
//	targetType := typ.Elem()
//	if targetType.Kind() != reflectlite.Interface && !targetType.Implements(errorType) {
//		panic("errors: *target must be interface or implement error")
//	}
//	return as(err, target, val, targetType)
//
// The model keeps the checks of err and target that need no reflection and
// moves the others into asAssign, which asWalk calls first, before calling any
// method of err: the same checks at the same point (no method of err is
// called between them), with the same panics.
func As(err error, target any) bool {
	if err == nil {
		return false
	}
	if target == nil {
		panic("errors: target cannot be nil")
	}
	return asWalk(err, target)
}

// MODEL: asWalk is Go's as (the tree walk; not translated), with its
// reflection (the parameters targetVal and targetType, and the test
//
//	if reflectlite.TypeOf(err).AssignableTo(targetType) {
//		targetVal.Elem().Set(reflectlite.ValueOf(err))
//		return true
//	}
//
// ) replaced by a call of asAssign, which does exactly this.
func asWalk(err error, target any) bool {
	for {
		if asAssign(err, target) {
			return true
		}
		if x, ok := err.(interface{ As(any) bool }); ok && x.As(target) {
			return true
		}
		switch x := err.(type) {
		case interface{ Unwrap() error }:
			err = x.Unwrap()
			if err == nil {
				return false
			}
		case interface{ Unwrap() []error }:
			for _, err := range x.Unwrap() {
				if err == nil {
					continue
				}
				if asWalk(err, target) {
					return true
				}
			}
			return false
		default:
			return false
		}
	}
}

// MODEL: asAssign checks target as Go's As does (panicking unless it is a
// non-nil pointer to an interface type or a type implementing error), then
// stores err into *target and returns true if err's dynamic type is assignable
// to the target's element type, and returns false otherwise. Trusted
// (Perennial/Code/errors.toml): its Lean model is the semantics' AsAssign
// (TrustedCode/errors.lean).
func asAssign(err error, target any) bool {
	val := reflectlite.ValueOf(target)
	typ := val.Type()
	if typ.Kind() != reflectlite.Ptr || val.IsNil() {
		panic("errors: target must be a non-nil pointer")
	}
	targetType := typ.Elem()
	if targetType.Kind() != reflectlite.Interface && !targetType.Implements(errorType) {
		panic("errors: *target must be interface or implement error")
	}
	if reflectlite.TypeOf(err).AssignableTo(targetType) {
		val.Elem().Set(reflectlite.ValueOf(err))
		return true
	}
	return false
}
