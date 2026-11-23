/-
Trusted code for the Go `crypto/sha1` package, in namespace `crypto.sha1` (as the generated
package): its `init`.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace crypto.sha1
section code
variable [GooseExts] [GoGlobalContext]

/-- `init` (`sha1.go`):

```go
func init() {
	crypto.RegisterHash(crypto.SHA1, New)
}
```

`RegisterHash(h, f)` panics if `h >= maxHash` (`crypto.SHA1` is in range) and otherwise stores
`f` in `crypto`'s table `hashes[h]`, which only `crypto.Hash.New` and `Hash.Available` read, so
that `crypto.SHA1.New()` finds sha1's `New`. The model does nothing: `crypto` is not translated
(its declarations, `Hash.New` and `Available` among them, are names only, so a call of one is
stuck), so no translated code reads the registration, and Go's `init` cannot panic. As
`crypto/sha256`'s `init.0` (TrustedCode/crypto/sha256.lean).

Why trusted: goose translates the real source, but proving it needs ownership of `crypto`'s
`hashes` in `crypto/sha1`'s initializer proof, and no ownership of another package's variable
reaches an init proof (`README.md`, trusted package-variable initializers). Accepted by the
owner's decision (2026-11-23), in place of threading an exclusive token for `hashes` through
every importer's init proof. -/
def init.«0».impl : val :=
  λ: <>, #()

end code
end crypto.sha1

end Perennial
