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

/-- The address of `MaxLen` (`internal/bytealg.MaxLen`, an `int`), which the generated package
names `MaxLen`; this file is imported by the generated package, so it cannot refer to that. -/
noncomputable def MaxLenAddr : Expr :=
  GlobalVarAddr go!"internal/bytealg.MaxLen" #()

/-- bytealg's `init` (in `index_amd64.go`, the only one on amd64):

```go
func init() {
	if cpu.X86.HasAVX2 {
		MaxLen = 63
	} else {
		MaxLen = 31
	}
}
```

`cpu.X86.HasAVX2` says whether the CPU has AVX2; the runtime sets it from `cpuid` (assembly)
before any package is initialized (`runtime.schedinit` → `cpuinit` → `cpu.Initialize`), which
no goose translation of a package runs. The model sets `MaxLen` to 63 or 31, chosen
arbitrarily, so it covers every CPU. -/
noncomputable def init.«0».impl : val :=
  λ: <>,
    if: ArbitraryInt =⟨go.int⟩ #(W64 0) then MaxLenAddr <-[go.int] #(W64 63)
    else MaxLenAddr <-[go.int] #(W64 31)

/-- `IndexByteString(s, c)`: the index of the first `c` in `s`, or `-1` if there is none. Go
implements it in assembly (`indexbyte_amd64.s`); the model is the loop

```go
for i := 0; i < len(s); i++ {
	if s[i] == c {
		return i
	}
}
return -1
``` -/
def IndexByteString.impl : val :=
  λ: "s" "c",
    (rec: "loop" "i" :=
      if: "i" <⟨go.int⟩ FuncResolve go.len [go.string] #() "s" then
        if: Index go.string ("s", "i") =⟨go.byte⟩ "c" then "i"
        else "loop" ("i" +⟨go.int⟩ #(W64 1))
      else #(W64 (-1))) #(W64 0)

/-- `CountString.loop s c i n`: `n` plus the number of `c`s in `s[i:]`. -/
def CountString.loop : val :=
  rec: "loop" "s" "c" "i" "n" :=
    if: "i" <⟨go.int⟩ FuncResolve go.len [go.string] #() "s" then
      "loop" "s" "c" ("i" +⟨go.int⟩ #(W64 1))
        (if: Index go.string ("s", "i") =⟨go.byte⟩ "c" then "n" +⟨go.int⟩ #(W64 1) else "n")
    else "n"

/-- `CountString(s, c)`: the number of `c`s in `s`. Go implements it in assembly
(`count_amd64.s`, which falls back to the Go `countGenericString` on a CPU without `POPCNT`);
the model is the loop

```go
n := 0
for i := 0; i < len(s); i++ {
	if s[i] == c {
		n++
	}
}
return n
``` -/
def CountString.impl : val :=
  λ: "s" "c", CountString.loop "s" "c" #(W64 0) #(W64 0)

/-- `IndexString(a, b)`: the index of the first occurrence of `b` in `a`, or `-1` if there is
none. Go implements it in assembly (`index_amd64.s`) and documents it as "Requires
2 <= len(b) <= MaxLen"; the model is undefined (`Panic`, stuck) unless that holds, which it
checks by reading `MaxLen` (Go's assembly does not read it), and otherwise is the loop

```go
n := len(b)
for i := 0; i <= len(a)-n; i++ {
	if a[i:i+n] == b {
		return i
	}
}
return -1
``` -/
noncomputable def IndexString.impl : val :=
  λ: "a" "b",
    let: "n" := FuncResolve go.len [go.string] #() "b" in
    if: ("n" <⟨go.int⟩ #(W64 2)) || (![go.int] MaxLenAddr <⟨go.int⟩ "n") then
      Panic "IndexString: undefined unless 2 <= len(b) <= MaxLen"
    else
      (rec: "loop" "i" :=
        if: "i" ≤⟨go.int⟩ FuncResolve go.len [go.string] #() "a" -⟨go.int⟩ "n" then
          if: Slice go.string ("a", "i", "i" +⟨go.int⟩ "n") =⟨go.string⟩ "b" then "i"
          else "loop" ("i" +⟨go.int⟩ #(W64 1))
        else #(W64 (-1))) #(W64 0)

/-- `abigen_runtime_cmpstring(a, b)` (`runtime.cmpstring`, which `CompareString` calls): `-1`,
`0` or `+1` as `a` is lexicographically less than, equal to or greater than `b`, comparing
bytes. Go implements it in assembly (`compare_amd64.s`); the model compares with Go's `<` and
`==` on strings, which are bytewise. -/
def abigen_runtime_cmpstring.impl : val :=
  λ: "a" "b",
    if: "a" <⟨go.string⟩ "b" then #(W64 (-1))
    else if: "a" =⟨go.string⟩ "b" then #(W64 0)
    else #(W64 1)

end code
end internal.bytealg

end Perennial
