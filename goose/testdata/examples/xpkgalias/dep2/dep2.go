// Package dep2 is imported by dep, but not by xpkgalias.
package dep2

type Y struct{ v uint64 }

type Box[T any] struct{ v T }
