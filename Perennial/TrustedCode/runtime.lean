/-
Trusted code for `runtime`: `Gosched.impl`, `buildVersion.init`, and the stack walk and
symbolization behind `Callers` and `CallersFrames` (`callers.impl`, `Frames.Next.impl`), in
namespace `runtime`, as the generated package.
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.TrustedCode.arbitraryString

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace runtime
section code
variable [GooseExts] [GoGlobalContext]

def Gosched.impl : val :=
  λ: <>,
    #()

/-- The initialization of `buildVersion` (`runtime/extern.go`), the string `Version` returns:

```go
// buildVersion is the Go tree's version string at build time.
// ...
// This is set by the linker.
var buildVersion string
```

The Go declaration has no initializer: the linker writes the value into the binary's data
(`cmd/link/internal/ld/main.go`: `addstrdata1(ctxt, "runtime.buildVersion="+buildVersion)`, with
`buildVersion` the toolchain's `buildcfg.Version`, the first line of `$GOROOT/VERSION` for a
release, plus `-X:<experiments>` when `GOEXPERIMENT` differs from the default), and `schedinit`
replaces an empty value by `"unknown"` before any package is initialized (`proc.go`). The linker's
`-X runtime.buildVersion=<s>` sets it to any string `s`, invalid UTF-8 included (Go evidence:
`goose/model/runtime/version_test.go`). Nothing writes it after that: `runtime` itself does not,
and a `//go:linkname` pull of it from another package is refused by the default linker (since Go
1.23; only `-ldflags=-checklinkname=0` allows it, and goose does not model `go:linkname`).

The model allocates the variable and stores an arbitrary string (`fmt.arbitraryString`, which can
be every string), so it is less defined than Go: every value Go can have is one of its results. It
cannot panic, nor can Go's (the value is in the binary). Goose runs it where it would allocate
a translated variable (before the imported packages' initializers), as for every trusted variable
without an initializer.

Why trusted: goose translates the declaration (a variable without an initializer is allocated
with its zero value), but that model would be unfaithful: `Version` would return `""`, where Go
returns the linker's string. The linker's write is not Go code. `Version` itself is translated. -/
noncomputable def buildVersion.init : val :=
  λ: <>,
    go.GlobalAlloc go!"runtime.buildVersion" go.string #() ;;
    GlobalVarAddr go!"runtime.buildVersion" #() <-[go.string] (fmt.arbitraryString #())

/-- `callers(skip int, pcbuf []uintptr) int` (`traceback.go`), which `Callers` (translated) calls
with a non-empty `pcbuf`: it walks the calling goroutine's stack (`systemstack`, the unwinder) and
writes the return program counters of the frames after the first `skip` into `pcbuf[0]`,
`pcbuf[1]`, ..., stopping at the end of the stack or of `pcbuf`, and returns how many it wrote
(`tracebackPCs`: `pcBuf[n] = pc` only for `n < len(pcBuf)`). It cannot panic: it writes nothing
past `len(pcbuf)`, and a `skip` past the stack's depth, or negative, writes fewer entries or the
whole buffer.

The model is goose's translation of

```go
func callers(skip int, pcbuf []uintptr) int {
	n := 0
	for n < len(pcbuf) && arbitrary() != 0 {
		pcbuf[n] = uintptr(arbitrary())
		n++
	}
	return n
}
```

with each call `arbitrary()` replaced by `ArbitraryInt` (an arbitrary `uint64`): it writes some
prefix of `pcbuf` with arbitrary words and returns its length, every `n` from `0` to
`len(pcbuf)` (Go: `n < len(pcbuf)` when the stack is shallower, `0` when `skip` is past it,
`len(pcbuf)` when the buffer is too short: `goose/model/runtime/callers_test.go`). It writes the
cells one at a time, as Go does, so a concurrent access to `pcbuf` races in the model as in Go.
Why trusted: the stack walk reads the goroutine's stack and the binary's tables, which the
semantics does not model. -/
noncomputable def callers.impl : val :=
  (LamV "skip"
  (Lam "pcbuf"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "pcbuf" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.uintptr)))) (Var "pcbuf"))
  (Let "skip" (App (Val (GoInstruction (GoAlloc go.int))) (Var "skip"))
  (Let "$r0" (Val #(W64 0))
  (Let "n" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int))) (Var "n"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (App (App (Val doFor) (Lam BAnon
  (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "n")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.uintptr)))) (Var "pcbuf"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.uintptr)]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair ArbitraryInt (Val #(W64 0))))) (Val #false)))) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.uint64 go.uintptr))) ArbitraryInt)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "n") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "n")) (Val #(W64 1)))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uintptr))) (Pair (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.uintptr)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.uintptr)))) (Var "pcbuf")) (App (Val (GoInstruction (GoLoad go.int))) (Var "n")))) (Var "$r0"))))))))
  (Lam BAnon
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "n") (Var "$r0"))))))))))
  (App (Val (GoInstruction (GoLoad go.int))) (Var "$res0"))))))

/-- `(*Frames).Next() (frame Frame, more bool)` (`symtab.go`): the next frame of the program
counters `ci.callers`, symbolized through the binary's tables (`findfunc`, the inlining tree,
the cgo symbolizer), and whether another one follows. It reads and writes `*ci` (`ci.callers`,
`ci.nextPC`, `ci.frames`), so a nil `ci` panics (nil dereference) and a concurrent call on the
same `Frames` races.

The model is goose's translation of

```go
func (ci *Frames) Next() (frame Frame, more bool) {
	ci.callers = ci.callers
	frame.PC = uintptr(arbitrary())
	if arbitrary() != 0 {
		frame.Func = arbitraryFuncPtr()
	}
	frame.Function = arbitraryString()
	frame.File = arbitraryString()
	frame.Line = int(arbitrary())
	frame.startLine = int(arbitrary())
	frame.Entry = uintptr(arbitrary())
	more = arbitrary() != 0
	return
}
```

with `arbitrary()` replaced by `ArbitraryInt`, `arbitraryString()` by `fmt.arbitraryString`
(every string), and `arbitraryFuncPtr()` by `GoPrealloc` (some non-null address, owning nothing:
code that dereferences `frame.Func` cannot be proved). The load and store of `ci.callers` make
it panic (stuck) on a nil `ci` and race with a concurrent access to `*ci`, as Go's; it leaves
`*ci` unchanged, where Go advances it, which no caller observes (the fields are unexported).
Every exported field of the frame (`PC`, `Func`, nil or not, `Function`, `File`, `Line`,
`Entry`) and `more` is arbitrary, a superset of what Go returns (`goose/model/runtime/callers_test.go`:
a nil `Func` for a frame of a function inlined into its caller, `Function`/`File`/`Line` of the
call sites, the zero frame with `more` false once the frames are exhausted); `funcInfo` is left
zero (unexported, read only by the runtime). Why trusted: symbolization reads the binary's
tables, which the semantics does not model. -/
noncomputable def Frames.Next.impl : val :=
  (LamV "ci"
  (Lam BAnon
  (Let "frame" (App (Val (GoInstruction (GoAlloc (go.GoType.Named go!"runtime.Frame" [])))) (App (Val (GoInstruction (GoZeroVal (go.GoType.Named go!"runtime.Frame" [])))) (Val #())))
  (Let "$res0" (Var "frame")
  (Let "more" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "$res1" (Var "more")
  (Seq (App (Val exceptionDo)
  (Let "ci" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType (go.GoType.Named go!"runtime.Frames" []))))) (Var "ci"))
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.uintptr)))) (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"runtime.Frames" []) go!"callers"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"runtime.Frames" []))))) (Var "ci"))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.uint64 go.uintptr))) ArbitraryInt)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val fmt.arbitraryString) (Val #()))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val fmt.arbitraryString) (Val #()))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.uint64 go.int))) ArbitraryInt)
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.uint64 go.int))) ArbitraryInt)
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.uint64 go.uintptr))) ArbitraryInt)
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair ArbitraryInt (Val #(W64 0)))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "more") (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uintptr))) (Pair (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"runtime.Frame" []) go!"Entry"))) (Var "frame")) (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"runtime.Frame" []) go!"startLine"))) (Var "frame")) (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"runtime.Frame" []) go!"Line"))) (Var "frame")) (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"runtime.Frame" []) go!"File"))) (Var "frame")) (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"runtime.Frame" []) go!"Function"))) (Var "frame")) (Var "$r0"))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair ArbitraryInt (Val #(W64 0))))))
  (Let "$r0" (App (Val (GoInstruction GoPrealloc)) (Val #()))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType (go.GoType.Named go!"runtime.Func" []))))) (Pair (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"runtime.Frame" []) go!"Func"))) (Var "frame")) (Var "$r0")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uintptr))) (Pair (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"runtime.Frame" []) go!"PC"))) (Var "frame")) (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.uintptr)))) (Pair (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"runtime.Frames" []) go!"callers"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"runtime.Frames" []))))) (Var "ci"))) (Var "$r0"))))))))
  (Pair (App (Val (GoInstruction (GoLoad (go.GoType.Named go!"runtime.Frame" [])))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res1"))))))))))

end code
end runtime

end Perennial
