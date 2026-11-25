// The Go model of internal/bytealg's init function (index_amd64.go's, the
// package's only one; Perennial/Code/internal/bytealg.toml, [model]), spliced
// into index_amd64.go in place of the real one.

package bytealg

import "internal/gomodel"

// MODEL: the package's init sets MaxLen to 63 or to 31. Go's
//
//	if cpu.X86.HasAVX2 {
//		MaxLen = 63
//	} else {
//		MaxLen = 31
//	}
//
// reads internal/cpu.X86, which no Go package initializer sets: the runtime
// fills it (cpu.Initialize, from schedinit) from the processor's cpuid
// (assembly) before any package is initialized. Goose translates the real
// init, but X86 would then stay zero and MaxLen always 31, more defined than
// gc. The model chooses (gomodel.Choose: the processor's AVX2 bit, which the
// semantics does not model) either value.
//
//gomodel:replace init.0 "if cpu.X86.HasAVX2 {"
func init() {
	if gomodel.Choose() {
		MaxLen = 63
	} else {
		MaxLen = 31
	}
}
