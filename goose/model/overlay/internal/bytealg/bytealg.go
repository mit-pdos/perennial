// The Go model of bytealg.MakeNoZero (Perennial/Code/internal/bytealg.toml,
// [model]), spliced into bytealg.go in place of the real declaration.

package bytealg

import "internal/gomodel"

// MODEL: MakeNoZero(n) is a slice of length n and capacity at least n whose
// bytes, up to the capacity, are not zeroed. Go's has no Go body (goose:
// "external function"): the runtime defines it (runtime/slice.go,
// `//go:linkname bytealg_MakeNoZero internal/bytealg.MakeNoZero`, which the
// overlay blanks so that gc links this body instead) as
//
//	if uintptr(len) > maxAlloc {
//		panicmakeslicelen()
//	}
//	cap := roundupsize(uintptr(len), true)
//	return unsafe.Slice((*byte)(mallocgc(cap, nil, false)), cap)[:len]
//
// The model chooses the capacity (gomodel.ChooseUint64: any c >= n, which
// includes the size class roundupsize rounds n up to) and each byte up to the
// capacity (gomodel.ChooseUint64: mallocgc with needzero false returns memory
// with whatever it held, which a Go program cannot predict). A negative n
// panics in make with Go's message ("makeslice: len out of range"). An n
// above maxAlloc (2^48), where gc panics, is not checked: the model
// allocates, as the semantics' make and append do (docs/KNOWN_LIMITATIONS.md,
// "No limit on allocation size", which names MakeNoZero).
func MakeNoZero(n int) []byte {
	c := int(gomodel.ChooseUint64() >> 1)
	if c < n {
		c = n
	}
	b := make([]byte, n, c)
	full := b[:cap(b)]
	for i := range full {
		full[i] = byte(gomodel.ChooseUint64())
	}
	return b
}
