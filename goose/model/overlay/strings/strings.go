// The Go model of strings.Split (Perennial/Code/strings.toml, [model]),
// spliced into strings.go in place of the real declaration.

package strings

import "internal/gomodel"

// MODEL: Split(s, sep) is the substrings of s between the occurrences of sep
// (found left to right, not overlapping), as Go's genSplit(s, sep, 0, -1)
// computes them. The model finds the occurrences by testing HasPrefix at each
// position, where Go's genSplit counts them with Count and finds them with
// Index. Goose translates the real Split, but at len(s) = 2^63-1 (a string gc
// cannot hold) genSplit's len(s)+1 overflows and it panics, so its spec would
// need a bound on len(s) that Split's spec does not have
// (Perennial/Code/strings.toml). The model returns the same fields as
// genSplit wherever genSplit does not panic, and there only: building such a
// string needs an allocation gc refuses, which the semantics allows
// (docs/KNOWN_LIMITATIONS.md, "No limit on allocation size"). For an empty
// sep, Go splits s into its UTF-8 sequences (explode); the model is stuck
// there, so every spec of Split requires sep to be non-empty.
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
