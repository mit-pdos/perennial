// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Go model of Index and IndexString, which internal/bytealg/index_native.go
// (go1.26.11) declares without a body: on linux/amd64 they are written in
// assembly (index_amd64.s). Go has no generic body for them (index_generic.go
// panics, on the architectures whose MaxLen is 0, where they are never
// called), so the bodies here are what their doc comments state, as a naive
// search. Outside their documented precondition 2 <= len(b) <= MaxLen the
// assembly's result is not specified, so there the model has no behaviour
// (gomodel.Stuck: less defined than Go, never more). The loop bound is
// `i <= len(a)-len(b)`, which cannot overflow (`i+len(b) <= len(a)` does for
// len(a) near the largest int, and the model would then slice out of range).
// Evidence: Go's own strings and bytes tests pass with the models in place of
// the assembly (goose/util TestModelBytealgDifftest).

package bytealg

import "internal/gomodel"

// MODEL: Index returns the index of the first instance of b in a, or -1 if b
// is not present in a. Requires 2 <= len(b) <= MaxLen.
func Index(a, b []byte) int {
	if len(b) < 2 || len(b) > MaxLen {
		gomodel.Stuck()
	}
	for i := 0; i <= len(a)-len(b); i++ {
		if string(a[i:i+len(b)]) == string(b) {
			return i
		}
	}
	return -1
}

// MODEL: IndexString returns the index of the first instance of b in a, or -1
// if b is not present in a. Requires 2 <= len(b) <= MaxLen.
func IndexString(a, b string) int {
	if len(b) < 2 || len(b) > MaxLen {
		gomodel.Stuck()
	}
	for i := 0; i <= len(a)-len(b); i++ {
		if a[i:i+len(b)] == b {
			return i
		}
	}
	return -1
}
