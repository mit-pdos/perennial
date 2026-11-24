// The Go model of errors.Is (Perennial/Code/errors.toml, [model]), spliced
// into wrap.go in place of the real declaration.

package errors

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
