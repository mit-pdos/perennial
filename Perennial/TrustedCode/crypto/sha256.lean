/-
Trusted code for the Go `crypto/sha256` package, in namespace `crypto.sha256` (as the generated
package), in terms of the SHA-256 extension (`Perennial/GooseLang/Ext/Sha256/Impl.lean`).

* `Sum256(data)` converts `data` to a string and hashes it with the extension's primitive
  (`ExternalOp sha256ExtName "Sum"`), which returns the `[32]byte` hash. Go's body runs the
  FIPS 140 implementation of SHA-256 (`crypto/internal/fips140/sha256`, or BoringCrypto),
  which the primitive stands for.
* `init.0` does nothing. Go's registers `New224` and `New` with `crypto.RegisterHash`, so that
  `crypto.SHA224.New()` and `crypto.SHA256.New()` find them; `crypto` is not translated, so no
  translated code reads the registration. It cannot panic (both hashes are in range).
-/
module

public import Perennial.Golang.Defn
public import Perennial.GooseLang.Ext.Sha256.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace crypto.sha256
section code
variable [GooseExts] [GoGlobalContext]

/-- Type: func([]byte) [32]byte -/
def Sum256.impl : val :=
  λ: "data", ExternalOp sha256ExtName "Sum" (Convert (go.SliceType go.byte) go.string "data")

def init.«0».impl : val :=
  λ: <>, #()

end code
end crypto.sha256

end Perennial
