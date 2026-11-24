// The Go model of strings.Split (Perennial/Code/strings.toml, [model]),
// spliced into strings.go in place of the real declaration.

package strings

import (
	"internal/gomodel"
	"unicode/utf8"
)

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

// MODEL: IndexRune(s, r) is the index of the first instance of the Unicode
// code point r in s, or -1. The first three cases are Go's, verbatim: an ASCII
// r is searched for as a byte, utf8.RuneError as the first rune a range loop
// over s decodes to RuneError (an invalid UTF-8 sequence, or U+FFFD itself),
// and an invalid r is in no string. Go's last case, a valid non-ASCII r, uses
// goto, which goose does not translate: it searches for the last byte of
// rs := string(r) with IndexByte, compares the bytes before it, and after
// bytealg.Cutover failed candidates hands the rest of s to
// bytealg.IndexString(s[i-last:], rs); each step skips only positions where rs
// does not start, so it returns the first index of rs in s, or -1. The model
// computes that with Index(s, string(r)) (stringslite.Index, whose search
// ends in the same bytealg.IndexString).
func IndexRune(s string, r rune) int {
	switch {
	case 0 <= r && r < utf8.RuneSelf:
		return IndexByte(s, byte(r))
	case r == utf8.RuneError:
		for i, r := range s {
			if r == utf8.RuneError {
				return i
			}
		}
		return -1
	case !utf8.ValidRune(r):
		return -1
	default:
		return Index(s, string(r))
	}
}
