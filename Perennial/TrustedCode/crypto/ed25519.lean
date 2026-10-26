/-
Trusted code for the Go `crypto/ed25519` package, in namespace `crypto.ed25519` (as the
generated package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace crypto.ed25519
section code
variable [GooseExts] [GoGlobalContext]

/-- The initializer of `cryptocustomrand` (`crypto/ed25519/ed25519.go`):

```go
var cryptocustomrand = godebug.New("cryptocustomrand")
```

The model does nothing, and `cryptocustomrand` is not allocated. `internal/godebug` is not
translated; its `New(name)` is `return &Setting{name: name}`, an allocation, so Go's
initializer cannot panic and has no effect beyond the variable. The variable's only reader is
`GenerateKey` (`cryptocustomrand.Value()`, which reads the `GODEBUG` setting the runtime hands
to `internal/godebug`), which is not translated; a translated reader could not load the
variable (nothing gives a points-to for it). -/
def cryptocustomrand.init : val :=
  λ: <>, #()

end code
end crypto.ed25519

end Perennial
