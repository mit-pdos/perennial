// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build amd64 || arm64 || loong64 || s390x || ppc64le || ppc64

// Go model of internal/bytealg/index_native.go (go1.26.11), which declares
// these two functions without a body: on linux/amd64 they are written in
// assembly (index_amd64.s). Go has no generic body for them (index_generic.go
// panics, on the architectures whose MaxLen is 0, where they are never
// called), so the bodies here are what their doc comments state, as a naive
// search. Evidence: ../../../bytealgdiff (a difftest against the real package,
// through strings).

package bytealg

// MODEL: Index returns the index of the first instance of b in a, or -1 if b
// is not present in a. Requires 2 <= len(b) <= MaxLen: the assembly's result
// outside it is not specified, so there the model does not terminate (less
// defined than Go, never more).
func Index(a, b []byte) int {
	if len(b) < 2 || len(b) > MaxLen {
		for {
		}
	}
	for i := 0; i+len(b) <= len(a); i++ {
		if string(a[i:i+len(b)]) == string(b) {
			return i
		}
	}
	return -1
}

// MODEL: IndexString returns the index of the first instance of b in a, or -1
// if b is not present in a. Requires 2 <= len(b) <= MaxLen: the assembly's
// result outside it is not specified, so there the model does not terminate
// (less defined than Go, never more).
func IndexString(a, b string) int {
	if len(b) < 2 || len(b) > MaxLen {
		for {
		}
	}
	for i := 0; i+len(b) <= len(a); i++ {
		if a[i:i+len(b)] == b {
			return i
		}
	}
	return -1
}
