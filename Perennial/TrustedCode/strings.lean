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
variable [GooseExts] [GoGlobalContext]

/-- `Join(elems, sep)`: the elements of `elems` separated by `sep`. Go's `Join` sums the
lengths, panics if the total overflows `int`, and copies into a `strings.Builder` (whose
`String()` is `unsafe.String`, which Goose does not translate). The model is goose's
translation of the same result computed with `+`:

```go
func Join(elems []string, sep string) string {
	var s string
	for i, e := range elems {
		if i > 0 {
			s += sep
		}
		s += e
	}
	return s
}
```

So it does not model the length-overflow panic: like `append` (`sumAssumeNoOverflowSigned`)
and string `+`, the model assumes a string's length fits in an `int`. -/
noncomputable def Join.impl : val :=
  (LamV "elems"
  (Lam "sep"
  (App (Val exceptionDo)
  (Let "sep" (App (Val (GoInstruction (GoAlloc go.string))) (Var "sep"))
  (Let "elems" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.string)))) (Var "elems"))
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.string))) (Var "s")))))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "elems"))
  (Let "e" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val (slice.forRange go.string)) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "s")) (App (Val (GoInstruction (GoLoad go.string))) (Var "e")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 0)))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "s")) (App (Val (GoInstruction (GoLoad go.string))) (Var "sep")))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (Var "$key")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "e") (Var "$value"))))))))))))))))))

/-- `HasPrefix(s, prefix)`: whether `s` begins with `prefix`. Go's `HasPrefix` is
`len(s) >= len(prefix) && s[:len(prefix)] == prefix` (in `internal/stringslite`); Goose's Go
semantics has no string slicing, so the model is goose's translation of the same test written
with byte indexing:

```go
func HasPrefix(s, prefix string) bool {
	if len(s) < len(prefix) {
		return false
	}
	var i int
	for i < len(prefix) {
		if s[i] != prefix[i] {
			return false
		}
		i++
	}
	return true
}
``` -/
noncomputable def HasPrefix.impl : val :=
  (LamV "s"
  (Lam "prefix"
  (App (Val exceptionDo)
  (Let "prefix" (App (Val (GoInstruction (GoAlloc go.string))) (Var "prefix"))
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (Var "s"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #true))))
  (App (App (App (Val doFor) (Lam BAnon
  (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "prefix"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))))) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "s")) (App (Val (GoInstruction (GoLoad go.int))) (Var "i")))) (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "prefix")) (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))))))))
  (App (Val doReturn)
  (Val #false))
  (App (Val doExecute)
  (Val #()))))))
  (Lam BAnon
  (Val #())))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "prefix"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))))
  (App (Val doReturn)
  (Val #false))
  (App (Val doExecute)
  (Val #())))))))))

/-- `Compare(a, b)`: `-1`, `0` or `+1` as `a` is lexicographically less than, equal to or
greater than `b`. Go implements it in `internal/bytealg` (`CompareString`, assembly); the model
compares with Go's `<` on strings, which is bytewise lexicographic, as `bytes.Compare`'s does. -/
def Compare.impl : val :=
  λ: "a" "b",
    if: "a" <⟨go.string⟩ "b" then #(W64 (-1))
    else if: "a" =⟨go.string⟩ "b" then #(W64 0)
    else #(W64 1)

/-- `TrimPrefix(s, prefix)`: `s` without the leading `prefix`, if it begins with it, else `s`.
Go's `TrimPrefix` (in `internal/stringslite`) returns `s[len(prefix):]`; Goose's Go semantics
has no string slicing, so the model is goose's translation of the same result computed through a
byte slice:

```go
func TrimPrefix(s, prefix string) string {
	if HasPrefix(s, prefix) {
		b := []byte(s)
		return string(b[len(prefix):])
	}
	return s
}
``` -/
noncomputable def TrimPrefix.impl : val :=
  (LamV "s"
  (Lam "prefix"
  (App (Val exceptionDo)
  (Let "prefix" (App (Val (GoInstruction (GoAlloc go.string))) (Var "prefix"))
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (Var "s"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.string))) (Var "s")))))
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Var "prefix"))
  (App (App (App (Val (GoInstruction (FuncResolve go!"strings.HasPrefix" []))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (Let "$r0" (App (Val (GoInstruction (Convert go.string (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoLoad go.string))) (Var "s")))
  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$s" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
  (App (Val (GoInstruction (Slice (go.GoType.SliceType go.byte)))) (Pair (Pair (Var "$s") (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "prefix"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0")))) (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.byte)]))) (Val #())) (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "b") (Var "$r0")))))))
  (App (Val doExecute)
  (Val #())))))))))

/-- `Split(s, sep)`: the substrings of `s` between the occurrences of `sep` (found left to right,
not overlapping), as Go's `Split` (`genSplit` with `Index`) computes them. Goose's Go semantics
has no string slicing, so the model is goose's translation of the same result computed through
byte slices:

```go
func Split(s, sep string) []string {
	_ = sep[0]
	var a []string
	var field string
	rest := s
	for len(rest) > 0 {
		if HasPrefix(rest, sep) {
			a = append(a, field)
			field = ""
			b := []byte(rest)
			rest = string(b[len(sep):])
			continue
		}
		field += string([]byte{rest[0]})
		b := []byte(rest)
		rest = string(b[1:])
	}
	return append(a, field)
}
```

Go splits `s` into its UTF-8 sequences when `sep` is empty; the model does not: its first
statement, `sep[0]`, is an index out of range for an empty `sep`, a run-time panic no proof can
get past (`wp_PanicOp`), so every spec of `Split` requires `sep` non-empty. -/
noncomputable def Split.impl : val :=
  (LamV "s"
  (Lam "sep"
  (App (Val exceptionDo)
  (Let "sep" (App (Val (GoInstruction (GoAlloc go.string))) (Var "sep"))
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (Var "s"))
  (Let "$r0" (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "sep")) (Val #(W64 0))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.string)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.string)))) (Val #())))
  (Let "field" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (Let "rest" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "a"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (GoLoad go.string))) (Var "field"))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string)))) (LiteralValue [(KeyedElement none (ElementExpression go.string (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType go.string)]))) (Val #())) (Var "$a0")) (Var "$a1")))))))
  (App (App (App (Val doFor) (Lam BAnon
  (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "rest"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))) (Val #(W64 0)))))) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.string (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoLoad go.string))) (Var "rest")))
  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$s" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
  (App (Val (GoInstruction (Slice (go.GoType.SliceType go.byte)))) (Pair (Pair (Var "$s") (Val #(W64 1))) (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.byte)]))) (Val #())) (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "rest") (Var "$r0")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "b") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "field") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "field")) (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "rest")) (Val #(W64 0))))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0")))]))))))))))))
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "rest"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Var "sep"))
  (App (App (App (Val (GoInstruction (FuncResolve go!"strings.HasPrefix" []))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "a"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (GoLoad go.string))) (Var "field"))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string)))) (LiteralValue [(KeyedElement none (ElementExpression go.string (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType go.string)]))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #(go!""))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.string (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoLoad go.string))) (Var "rest")))
  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$s" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
  (App (Val (GoInstruction (Slice (go.GoType.SliceType go.byte)))) (Pair (Pair (Var "$s") (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "sep"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0")))) (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.byte)]))) (Val #())) (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b")))))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doContinue) (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "rest") (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "b") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "field") (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.string)))) (Pair (Var "a") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (Lam BAnon
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "rest") (Var "$r0")))))))))))
  (App (Val doExecute)
  (Var "$r0")))))))))

/-- `(*Builder).copyCheck()`: panics if `b` is a copy by value of a Builder that has been
written to; on first use, records `b` in `b.addr`. Go's (`strings/builder.go`)

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

Goose translates it, but the translation is stuck at the conversion of an `unsafe.Pointer` back to
`*Builder`: the semantics converts an `unsafe.Pointer` only to a pointer to a plain type
(`Golang/Defn/Plain.lean`, `convert_unsafe_to_pointer`), and `Builder` (a pointer and a slice) is
not one. The model is goose's translation of that code with
`(*Builder)(abi.NoEscape(unsafe.Pointer(b)))` replaced by `b`, and one addition: after setting
`b.addr`, it leaves a reader on the field `b.addr` for good (`StartRead` with no `FinishRead`), so
that any later store to `b.addr` is stuck (loads still step). (`(go.GoType.Named go!"strings.Builder"
[])` is written out: `Code/strings.lean` imports this file.)

**Why the reader.** `abi.NoEscape` hides `b` from escape analysis, so a `Builder` that does not
otherwise escape lives on its goroutine's stack, and `b.addr` points into that stack. When the
stack grows, gc moves it and rewrites the pointers in the stack's own frames (`b.addr` among them,
together with `b`), but not pointers into the stack held elsewhere. A copy by value of a used
Builder kept outside the stack therefore holds a stale `addr`, and storing it back over `b` makes
the next `copyCheck` panic (`goose/model/strings/builder_alias_test.go`,
`TestBuilderStaleCopyPanics`):
```go
var saved strings.Builder // a package variable: on the heap
b.WriteString("a"); saved = b; deep(10000); b = saved; b.WriteString("c") // panics
```
With `b.addr = b` alone the model would let that `WriteString` succeed: it would be more defined
than Go. With the reader, the store `b = saved` is stuck instead. In the model, `copyCheck` at `b`
passes with a non-nil `b.addr` only if `copyCheck` at `b` set it and nothing has stored to `b.addr`
since (every store after the first is stuck, and before it no value with `addr = b` exists: only
`copyCheck` at `b` makes one, and `addr` is unexported). In gc that `b.addr` is `b`'s own field,
set to `&b` and moved with `b` if the stack moves, so gc's check passes too. Everywhere else the
model is less defined than Go, never more:
- storing a copy back over a used Builder (`b = saved`, `b = strings.Builder{}`) is stuck, though
  gc does not panic when the stack has not moved;
- a copy stored into a Builder at another address keeps `addr` pointing to the original, so the
  model's `copyCheck` panics there; gc's may not, when that address is where the original was (a
  stack slot reused, as by a `var b strings.Builder` inside a loop: the model allocates a fresh
  location each time and never reuses one);
- `Reset` (`Builder.Reset.impl`) leaves `b.addr` set, where Go clears it, so that a copy of a
  Builder reset after use panics in the model, not in Go. -/
noncomputable def Builder.copyCheck.impl : val :=
  (LamV "b"
  (Lam BAnon
  (Seq (App (Val exceptionDo)
  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Var "b"))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"strings.Builder" []) go!"addr"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Var "b")))) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Val UntypedNil)))))
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Var "b"))
  (App (Val doExecute)
  (Seq (App (Val (GoInstruction (GoStore (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Pair (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"strings.Builder" []) go!"addr"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Var "b"))) (Var "$r0")))
  (Seq (StartRead (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"strings.Builder" []) go!"addr"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Var "b"))))
  (Val #())))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"strings.Builder" []) go!"addr"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Var "b")))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Var "b"))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (Convert go.string (go.GoType.InterfaceType [])))) (Val #(go!"strings: illegal use of non-zero Builder copied by value")))
  (App (App (Val (GoInstruction (FuncResolve go.panic []))) (Val #())) (Var "$a0"))))
  (App (Val doExecute)
  (Val #()))))))
  (Val #()))))

/-- `(*Builder).Reset()`: the Builder is empty again. Go's (`strings/builder.go`)

```go
func (b *Builder) Reset() {
	b.addr = nil
	b.buf = nil
}
```

The model is goose's translation of that code without `b.addr = nil`: `copyCheck`'s model leaves a
reader on `b.addr` once it is set, so that store would be stuck (`Builder.copyCheck.impl` says
why). Keeping `addr` only makes the model less defined: `addr` is unexported and only `copyCheck`
reads it, which at `b` passes alike for `addr = b` and nil, and panics for a copy whose `addr` is
`b` where Go's, whose `addr` is nil, would not. -/
noncomputable def Builder.Reset.impl : val :=
  (LamV "b"
  (Lam BAnon
  (Seq (App (Val exceptionDo)
  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Var "b"))
  (Let "$r0" (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.SliceType go.byte)))) (Val UntypedNil))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"strings.Builder" []) go!"buf"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Var "b"))) (Var "$r0")))))))
  (Val #()))))

/-- Leaves a reader on each element of `s[i:len(s)]`, for good (a helper of `Builder.String.impl`,
not a function of package `strings`): `StartRead` with no `FinishRead`, so that loads of those
bytes still step and stores to them are stuck. -/
noncomputable def Builder.readLock : val :=
  rec: "loop" "s" "i" :=
    if: "i" <⟨go.int⟩ FuncResolve go.len [go.SliceType go.byte] #() "s" then
      StartRead (IndexRef (go.SliceType go.byte) ("s", "i")) ;;
      "loop" "s" ("i" +⟨go.int⟩ #(W64 1))
    else #()

/-- `(*Builder).String()`: the accumulated string. Go's (`strings/builder.go`)

```go
func (b *Builder) String() string {
	return unsafe.String(unsafe.SliceData(b.buf), len(b.buf))
}
```

returns a string that shares the buffer's bytes; goose rejects `unsafe.String` (an `unsafe`
reinterpretation of a byte array as a string). The rest of `Builder` is goose's translation of
the real source.

The model returns `string(b.buf)`, a copy, and then leaves a reader on each byte of `b.buf`
(`Builder.readLock`), so that any later store to one of those bytes is stuck. Go strings are
immutable only while nothing writes the bytes they share: after
```go
b.WriteString("a"); saved := b; b.WriteString("b"); s := b.String()
b = saved; b.WriteString("c")   // copyCheck passes: b.addr == &b
```
gc's `s` is `"ac"`, where a copy would stay `"ab"`. `Builder` itself only appends past `len(b.buf)`;
the bytes the string shares are written again only through a Builder restored from a copy by
value (as above), and in the model that write is stuck: the model is less defined than Go there,
never different. Loads of the bytes (more `String` calls, `grow`'s copy) still step. (Since
`copyCheck`'s model leaves a reader on `b.addr`, the restore `b = saved` above is itself stuck in
the model; the readers on the bytes keep `String`'s model correct on its own, whatever the
model of `copyCheck`.) -/
noncomputable def Builder.String.impl : val :=
  λ: "b" <>,
    let: "buf" := ![go.SliceType go.byte]
      (StructFieldRef (go.Named go!"strings.Builder" []) go!"buf" "b") in
    let: "s" := Convert (go.SliceType go.byte) go.string "buf" in
    Builder.readLock "buf" #(W64 0) ;;
    "s"

end code
end strings

end Perennial
