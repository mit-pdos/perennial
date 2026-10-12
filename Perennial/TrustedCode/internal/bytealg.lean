/-
Trusted model of `internal/bytealg` (namespace `internal.bytealg`, as the generated package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace internal.bytealg
section code
variable [FfiSyntax] [GoGlobalContext]

/-- Go's largest allocation on 64-bit Linux (`runtime.maxAlloc`, `1 << heapAddrBits` with
`heapAddrBits = 48`). -/
def maxAlloc : Int := 2 ^ 48

/-- `MakeNoZero(n)`: a new `[]byte` of length `n` and capacity at least `n`. Go's `MakeNoZero`
has no Go body; the runtime implements it (`runtime.bytealg_MakeNoZero`):

```go
func bytealg_MakeNoZero(len int) []byte {
	if uintptr(len) > maxAlloc {
		panicmakeslicelen()
	}
	cap := roundupsize(uintptr(len), true)
	return unsafe.Slice((*byte)(mallocgc(cap, nil, false)), cap)[:len]
}
```

The model panics where Go does (`n` negative or above `maxAlloc`; a run-time panic, so stuck,
like `make`'s), and otherwise is `make([]byte, n, c)` for an arbitrary `c ≥ n`
(`slice._new_cap`), which includes every capacity `roundupsize` can give. Go does not zero the
bytes; the model does. That is unobservable to a caller that writes every byte before reading
it, as the only translated caller, `strings.Builder.grow`, does (it reads nothing past what
`copy` and `append` wrote); a new caller must be checked for the same. Go's `maxAlloc` is
smaller on some other platforms (`2^40` on iOS); the model follows 64-bit Linux. -/
def MakeNoZero.impl : val :=
  λ: "n",
    if: "n" <⟨go.int⟩ #(W64 0) then Panic "makeslice: len out of range" else #() ;;
    if: #(W64 maxAlloc) <⟨go.int⟩ "n" then Panic "makeslice: len out of range" else #() ;;
    FuncResolve go.make3 [go.SliceType go.byte] #() "n" (slice._new_cap "n")

end code
end internal.bytealg

end Perennial
