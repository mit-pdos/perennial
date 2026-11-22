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
variable [GooseExts] [GoGlobalContext]

/-- Stores an arbitrary byte in each element of `s[i:len(s)]` (a helper of `MakeNoZero.impl`,
not a function of package `internal/bytealg`). -/
noncomputable def fillArbitrary : val :=
  rec: "loop" "s" "i" :=
    if: "i" <⟨go.int⟩ FuncResolve go.len [go.SliceType go.byte] #() "s" then
      IndexRef (go.SliceType go.byte) ("s", "i")
        <-[go.byte] Convert go.uint64 go.byte ArbitraryInt ;;
      "loop" "s" ("i" +⟨go.int⟩ #(W64 1))
    else #()

/-- `MakeNoZero(n)`: a slice of length `n` and capacity at least `n` whose bytes, up to the
capacity, are not zeroed. It is a `go:linkname` to the runtime with no Go body, which goose
rejects ("external function"); the runtime's `bytealg_MakeNoZero` (`runtime/slice.go`):

```go
func bytealg_MakeNoZero(len int) []byte {
	if uintptr(len) > maxAlloc {
		panicmakeslicelen()
	}
	cap := roundupsize(uintptr(len), true)
	return unsafe.Slice((*byte)(mallocgc(cap, nil, false)), cap)[:len]
}
```

The model: `make([]byte, n, c)` for an arbitrary `c ≥ n` (the size class gc rounds up to, which
the model does not follow: `slice._new_cap`, as `append`'s new capacity), then an arbitrary byte
in every element up to `c` (`mallocgc` with `needzero` false returns memory with whatever it
held). Where it departs from Go:
- A negative `n` panics (`make3`'s "makeslice: len out of range", Go's message too). An `n`
  above `maxAlloc` (2^48), where gc panics, is not: the model allocates, as `make` does
  (allocation bounds are not modelled, `docs/KNOWN_LIMITATIONS.md`).
- Bytes are values the model chooses, where gc's are the memory's earlier contents: the same
  set of outcomes, since a Go program cannot tell which. -/
noncomputable def MakeNoZero.impl : val :=
  λ: "n",
    let: "s" := FuncResolve go.make3 [go.SliceType go.byte] #() "n" (slice._new_cap "n") in
    fillArbitrary (Slice (go.SliceType go.byte)
      ("s", #(W64 0), FuncResolve go.cap [go.SliceType go.byte] #() "s")) #(W64 0) ;;
    "s"

/-- The package's `init` (`init.0`): sets `MaxLen` to 63 or to 31. Go's (`index_amd64.go`; the
semantics is gc's for linux/amd64)

```go
func init() {
	if cpu.X86.HasAVX2 {
		MaxLen = 63
	} else {
		MaxLen = 31
	}
}
```

reads `cpu.X86.HasAVX2`, which the runtime sets from the processor's `cpuid` (assembly) before
any package is initialized. The model chooses either value: the machine is not modelled. -/
noncomputable def init.«0».impl : val :=
  λ: <>,
    (GlobalVarAddr go!"internal/bytealg.MaxLen" #())
      <-[go.int] (if: ArbitraryInt =⟨go.int64⟩ #(W64 0) then #(W64 63) else #(W64 31))

end code
end internal.bytealg

end Perennial
