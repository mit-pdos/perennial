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

which goose does not translate (`unsafe.String`: "builtin that isn't an ident"). The model is
goose's translation of

```go
func (b *Builder) String() string {
	return string(b.buf)
}
```

(the receiver's type written out as `strings.Builder`'s named type, which this file cannot refer
to by its generated name `Builder.ty`), with `b.buf` bound to `buf` and `lockBytes buf 0` run
before the conversion. Go's result shares `b.buf`'s bytes where the model's is a copy. The two
differ only if one of those bytes is written after `String` reads `b.buf`, which a `Builder` used
through one address never does (`WriteString` appends past `len(b.buf)`, `grow` copies to a new
buffer). A copy of the struct can: after `saved := b`, `b.WriteString`, `s := b.String()`,
`b = saved`, a `b.WriteString` writes into the bytes `s` aliases, changing `s` in Go; so can a
write through `saved` in another goroutine while `String` runs on a third copy (no race in Go:
`String` reads only the header). `lockBytes` read-locks those bytes before the conversion reads
them, so every such write either lands before the copy (and Go's `s` sees it too) or is stuck.
Both dereference `b` (a nil `b` panics in Go and is stuck in the model). -/
noncomputable def Builder.String.impl : val :=
  (LamV "b"
  (Lam BAnon
  (App (Val exceptionDo)
  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Var "b"))
  (Let "buf" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"strings.Builder" []) go!"buf"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"strings.Builder" []))))) (Var "b"))))
  (Seq (App (App (Val Builder.String.lockBytes) (Var "buf")) (Val #(W64 0)))
  (App (Val doReturn)
  (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Var "buf")))))))))

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

end code
end strings

end Perennial
