/-
Trusted code for `runtime`: `Gosched.impl` and `buildVersion.init`, in namespace `runtime`, as
the generated package.
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
`goose/model/runtime/version_test.go`). Nothing writes it after that.

The model allocates the variable and stores an arbitrary string (`fmt.arbitraryString`, which can
be every string), so it is less defined than Go: every value Go can have is one of its results. It
cannot panic, nor can Go's (the value is in the binary). Goose runs it where it would allocate
a translated variable (before the imported packages' initializers), as for every trusted variable
without an initializer. -/
def buildVersion.init : val :=
  λ: <>,
    go.GlobalAlloc go!"runtime.buildVersion" go.string #() ;;
    GlobalVarAddr go!"runtime.buildVersion" #() <-[go.string] (fmt.arbitraryString #())

end code
end runtime

end Perennial
