/-
Trusted code for `github.com/mit-pdos/perennial/goose/testdata/examples/skipinit/dep`, in
namespace `github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.dep` (as the generated
package): the initializer of `X`, which the model skips.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.dep
section code
variable [GooseExts] [GoGlobalContext]

/-- The initializer of `X` (`dep.go`):

```go
var X = newX()
```

The model skips it (`go.skipInit`): `X` is not allocated. `newX` allocates a `uint64` and
returns a pointer to it, so Go's initializer cannot panic and has no effect beyond the variable.
Package `user` shows what a proof can still do with `X`: take its address, and reach code that
would load it only in a branch the proof shows is not taken. -/
def X.init : val := go.skipInit

end code
end github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.dep

end Perennial
