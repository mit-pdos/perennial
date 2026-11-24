// The Go model of three methods of strings.Builder
// (Perennial/Code/strings.toml, [model]), spliced into builder.go in place of
// the real declarations. The rest of Builder is the real Go, translated.

package strings

import "internal/gomodel"

// MODEL: Go's copyCheck panics if b is a copy by value of a Builder that has
// been written to, and on first use records b in b.addr. Go's is
//
//	if b.addr == nil {
//		b.addr = (*Builder)(abi.NoEscape(unsafe.Pointer(b)))
//	} else if b.addr != b {
//		panic("strings: illegal use of non-zero Builder copied by value")
//	}
//
// Goose translates it, but the translation is stuck at the conversion of an
// unsafe.Pointer back to *Builder: the semantics converts an unsafe.Pointer
// only to a pointer to a plain type (Golang/Defn/Plain.lean), and Builder (a
// pointer and a slice) is not one. The model writes b for that conversion,
// and after setting b.addr makes it read-only for good (gomodel.StartRead), so
// that any later store to b.addr is stuck (loads still step). Where Go's check
// fails, the model is stuck (gomodel.Stuck) instead of panicking: Go's panic
// can be recovered, and the model cannot tell whether gc's check fails (see
// below), so a model panic where gc's check passes would be a behaviour Go
// does not have.
//
// Why read-only: abi.NoEscape hides b from escape analysis, so a Builder that
// does not otherwise escape lives on its goroutine's stack, and b.addr points
// into that stack. When the stack grows, gc moves it and rewrites the pointers
// in the stack's own frames (b.addr among them, together with b), but not
// pointers into the stack held elsewhere. A copy by value of a used Builder
// kept outside the stack therefore holds a stale addr, and storing it back
// over b makes the next copyCheck panic (goose/model/strings/
// builder_alias_test.go, TestBuilderStaleCopyPanics):
//
//	var saved strings.Builder // a package variable: on the heap
//	b.WriteString("a"); saved = b; deep(10000); b = saved; b.WriteString("c") // panics
//
// With b.addr = b alone the model would let that WriteString succeed: it would
// be more defined than Go. With b.addr read-only, the store b = saved is stuck
// instead. In the model, copyCheck at b passes with a non-nil b.addr only if
// copyCheck at b set it and nothing has stored to b.addr since (every store
// after the first is stuck, and before it no value with addr = b exists: only
// copyCheck at b makes one, and addr is unexported). In gc that b.addr is b's
// own field, set to &b and moved with b if the stack moves, so gc's check
// passes too. Everywhere else the model is stuck, so less defined than Go,
// never more:
//   - storing a copy back over a used Builder (b = saved, b = strings.Builder{})
//     is stuck, though gc does not panic when the stack has not moved;
//   - a copy stored into a Builder at another address keeps addr pointing to
//     the original, so the model's copyCheck is stuck there, where gc's
//     panics, or passes when that address is where the original was (a stack
//     slot reused, as by a var b strings.Builder inside a loop: the model
//     allocates a fresh location each time and never reuses one);
//   - Reset leaves b.addr set, where Go clears it, so that the model's
//     copyCheck is stuck at a copy of a Builder reset after use, where Go's
//     passes.
func (b *Builder) copyCheck() {
	if b.addr == nil {
		b.addr = b
		gomodel.StartRead(&b.addr)
	} else if b.addr != b {
		gomodel.Stuck()
	}
}

// MODEL: String returns the accumulated string. Go's is
//
//	return unsafe.String(unsafe.SliceData(b.buf), len(b.buf))
//
// which returns a string that shares the buffer's bytes; goose does not
// translate unsafe.String (a reinterpretation of a byte array as a string).
// The model returns string(b.buf), a copy, and then makes each byte of b.buf
// read-only for good (gomodel.StartRead), so that any later store to one of
// them is stuck. Go strings are immutable only while nothing writes the bytes
// they share: after
//
//	b.WriteString("a"); saved := b; b.WriteString("b"); s := b.String()
//	b = saved; b.WriteString("c")   // copyCheck passes: b.addr == &b
//
// gc's s is "ac", where a copy would stay "ab". Builder itself only appends
// past len(b.buf); the bytes the string shares are written again only through
// a Builder restored from a copy by value (as above), and in the model that
// write is stuck: the model is less defined than Go there, never different.
// Loads of the bytes (more String calls, grow's copy) still step. (Since
// copyCheck's model makes b.addr read-only, the restore b = saved above is
// itself stuck in the model; the read-only bytes keep String's model correct
// on its own, whatever the model of copyCheck.)
func (b *Builder) String() string {
	buf := b.buf
	s := string(buf)
	for i := range buf {
		gomodel.StartRead(&buf[i])
	}
	return s
}

// MODEL: Reset empties the Builder. Go's is
//
//	b.addr = nil
//	b.buf = nil
//
// The model leaves out b.addr = nil: copyCheck's model makes b.addr read-only
// once it is set, so that store would be stuck. Keeping addr only makes the
// model less defined: addr is unexported and only copyCheck reads it, which
// at b passes alike for addr = b and nil, and is stuck at a copy whose addr is
// b where Go's, whose addr is nil, passes.
func (b *Builder) Reset() {
	b.buf = nil
}
