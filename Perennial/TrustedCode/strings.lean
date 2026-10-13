/-
Trusted code for the Go `strings` package, in namespace `strings` (as the generated
package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace strings
section code
variable [FfiSyntax] [GoGlobalContext]

/-- `lockBytes buf i` read-locks `buf[i]`, ..., `buf[len(buf)-1]` and never unlocks them: each
`StartRead` is left without its `FinishRead`, so any later write to one of those bytes is stuck
(a write starts with `PrepareWrite`, which needs the location to have no readers, `PrepareWriteS`
in `Lang.lean`), while reads still go through. -/
def Builder.String.lockBytes : val :=
  rec: "lock" "buf" "i" :=
    if: "i" <⟨go.int⟩ FuncResolve go.len [go.SliceType go.byte] #() "buf" then
      StartRead (IndexRef (go.SliceType go.byte) ("buf", "i")) ;;
      "lock" "buf" ("i" +⟨go.int⟩ #(W64 1))
    else #()

/-- `b.String()`: the bytes written to the builder `b`. Go's `String` is

```go
func (b *Builder) String() string {
	return unsafe.String(unsafe.SliceData(b.buf), len(b.buf))
}
```

which goose does not translate (`unsafe.String`: "builtin that isn't an ident"). The model
loads `b.buf` (the receiver's type written out as `strings.Builder`'s named type, which this
file cannot refer to by its generated name `Builder.ty`), runs `lockBytes buf 0`, and returns
`string(buf)`, a copy of the bytes. Go's result shares `b.buf`'s bytes where the model's is a
copy. The two differ only if one of those bytes is written after `String` reads `b.buf`, which a
`Builder` used through one address never does (`WriteString` appends past `len(b.buf)`, `grow`
copies to a new buffer). A copy of the struct can: after `saved := b`, `b.WriteString`,
`s := b.String()`, `b = saved`, a `b.WriteString` writes into the bytes `s` aliases, changing
`s` in Go. (A write through the copy `saved` itself panics in `copyCheck`, `saved.addr` being
`&b`; the aliasing write goes through `b` again.) `lockBytes` read-locks those bytes before
the conversion reads them, so every such write either lands before the copy (and Go's `s` sees
it too) or is stuck. Both dereference `b` (a nil `b` panics in Go and is stuck in the
model). -/
noncomputable def Builder.String.impl : val :=
  λ: "b" <>,
    let: "buf" := ![go.SliceType go.byte]
      (StructFieldRef (go.GoType.Named go!"strings.Builder" []) go!"buf" "b") in
    Builder.String.lockBytes "buf" #(W64 0) ;;
    Convert (go.SliceType go.byte) go.string "buf"

/-- Model of (strings/builder.go)

```go
func (b *Builder) copyCheck() {
	if b.addr == nil {
		// This hack works around a failing of Go's escape analysis
		// that was causing b to escape and be heap allocated.
		// See issue 23382.
		// TODO: once issue 7921 is fixed, this should be reverted to
		// just "b.addr = b".
		b.addr = (*Builder)(abi.NoEscape(unsafe.Pointer(b)))
	} else if b.addr != b {
		panic("strings: illegal use of non-zero Builder copied by value")
	}
}
```

Goose translates it, but the semantics does not convert an `unsafe.Pointer` to a
`*Builder` (`go.Reinterpretable`: a `Builder` holds a pointer). The conversion is a round
trip of `b` (`abi.NoEscape` returns its argument), so the model stores `b`, the comment's
`b.addr = b`. A lower rung would need `unsafe.Pointer` values to carry the type they were
converted from, which the semantics does not model. The model loads `b.addr` once where the
source reads it twice (gc compiles the two reads as one load, and nothing writes it in
between in a `Builder` used through one address). The panic, not recovered, is stuck, as in
goose's translation. -/
noncomputable def Builder.copyCheck.impl : val :=
  λ: "b" <>,
    let: "addr" := StructFieldRef (go.GoType.Named go!"strings.Builder" []) go!"addr" "b" in
    let: "a" := ![go.PointerType (go.GoType.Named go!"strings.Builder" [])] "addr" in
    if: "a" =⟨go.PointerType (go.GoType.Named go!"strings.Builder" [])⟩ #null then
      "addr" <-[go.PointerType (go.GoType.Named go!"strings.Builder" [])] "b"
    else if: "a" =⟨go.PointerType (go.GoType.Named go!"strings.Builder" [])⟩ "b" then #()
    else Panic "strings: illegal use of non-zero Builder copied by value"

end code
end strings

end Perennial
