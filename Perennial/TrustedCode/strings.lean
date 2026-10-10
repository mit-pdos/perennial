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

end code
end strings

end Perennial
