// The Go model of strings' Join and Split (Perennial/Code/strings.toml,
// [model]), spliced into strings.go in place of the real declarations.

package strings

import "internal/gomodel"

// MODEL: Join(elems, sep) is the elements of elems separated by sep, computed
// with string +. Go's Join sums the lengths first, panics if the total
// overflows int, and then copies into a Builder. The model does not have the
// overflow panic, which a program can reach (a few gigabytes of aliased
// elements with a long separator): a known departure, where the model is more
// defined than Go (README.md, "Model assumptions (overflow)").
// Translating the real Join (its Builder calls are translated now) would
// remove it, at the cost of a premise on wp_Join excluding the overflow.
func Join(elems []string, sep string) string {
	var s string
	for i, e := range elems {
		if i > 0 {
			s += sep
		}
		s += e
	}
	return s
}

// MODEL: Split(s, sep) is the substrings of s between the occurrences of sep
// (found left to right, not overlapping), as Go's genSplit(s, sep, 0, -1)
// computes them. The model finds the occurrences by testing HasPrefix at each
// position: Go's genSplit counts them with Count and finds them with Index,
// both of which end in internal/bytealg's assembly. For an empty sep, Go
// splits s into its UTF-8 sequences (explode); the model is stuck there, so
// every spec of Split requires sep to be non-empty.
func Split(s, sep string) []string {
	if len(sep) == 0 {
		gomodel.Stuck()
	}
	var a []string
	var field string
	rest := s
	for len(rest) > 0 {
		if HasPrefix(rest, sep) {
			a = append(a, field)
			field = ""
			rest = rest[len(sep):]
			continue
		}
		field += rest[:1]
		rest = rest[1:]
	}
	return append(a, field)
}
