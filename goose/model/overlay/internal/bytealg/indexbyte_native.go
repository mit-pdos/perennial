// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build 386 || (amd64 && !plan9) || s390x || arm || arm64 || loong64 || ppc64 || ppc64le || mips || mipsle || mips64 || mips64le || riscv64 || wasm

// Go model of internal/bytealg/indexbyte_native.go (go1.26.11), which declares
// these two functions without a body: on linux/amd64 they are written in
// assembly (indexbyte_amd64.s). The bodies are Go's own generic fallbacks,
// verbatim from indexbyte_generic.go (the file the build constraint above
// excludes on amd64), so that goose translates Go instead of a hand-written
// Lean model. Evidence: ../../../bytealgdiff (a difftest against the real
// package, through strings).

package bytealg

// MODEL: IndexByte returns the index of the first instance of c in b, or -1
// if c is not present in b. Go's generic body (indexbyte_generic.go); the
// assembly computes the same function, deterministically.
func IndexByte(b []byte, c byte) int {
	for i, x := range b {
		if x == c {
			return i
		}
	}
	return -1
}

// MODEL: IndexByteString returns the index of the first instance of c in s,
// or -1 if c is not present in s. Go's generic body (indexbyte_generic.go);
// the assembly computes the same function, deterministically.
func IndexByteString(s string, c byte) int {
	for i := 0; i < len(s); i++ {
		if s[i] == c {
			return i
		}
	}
	return -1
}
