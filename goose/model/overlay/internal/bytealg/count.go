// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Go model of Count and CountString, which internal/bytealg/count_native.go
// (go1.26.11) declares without a body: on linux/amd64 they are written in
// assembly (count_amd64.s, which falls back to count_native.go's countGeneric
// and countGenericString without POPCNT). The bodies are Go's own generic
// fallbacks, verbatim from count_generic.go (the file whose build constraint
// excludes amd64), so that goose translates Go instead of a hand-written Lean
// model. Evidence: Go's own strings and bytes tests pass with the models in
// place of the assembly (etc/model-tests.sh, goose/util
// TestModelBytealgDifftest).

package bytealg

// MODEL: Count returns the number of instances of c in b. Go's generic body
// (count_generic.go); the assembly computes the same function,
// deterministically.
func Count(b []byte, c byte) int {
	n := 0
	for _, x := range b {
		if x == c {
			n++
		}
	}
	return n
}

// MODEL: CountString returns the number of instances of c in s. Go's generic
// body (count_generic.go); the assembly computes the same function,
// deterministically.
func CountString(s string, c byte) int {
	n := 0
	for i := 0; i < len(s); i++ {
		if s[i] == c {
			n++
		}
	}
	return n
}
