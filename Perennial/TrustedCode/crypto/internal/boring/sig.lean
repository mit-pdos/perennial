/-
Trusted code for the Go `crypto/internal/boring/sig` package, in namespace
`crypto.internal.boring.sig` (as the generated package): `StandardCrypto`, which
`crypto/internal/boring.Unreachable` calls.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace crypto.internal.boring.sig
section code
variable [GooseExts] [GoGlobalContext]

/-- `StandardCrypto()` (`sig.go`: `func StandardCrypto()`, no Go body): an assembly function
(`sig_amd64.s`) whose body is a marker for tools that inspect the binary:

```
TEXT ·StandardCrypto(SB),NOSPLIT,$0
	START                    // BYTE $0xEB; BYTE $0x1D; ... (a short jump over the marker)
	BYTE $0xba; ...          // 24 bytes of marker
	END                      // BYTE $0xC3 (RET)
```

`START` is `JMP +0x1D` (`EB 1D`) followed by five bytes `F4 48 F4 4B F4`; the jump skips those
five and the 24 marker bytes, 29 = 0x1D in all, and lands on `END`, a `RET`. So the function
returns at once: it takes no argument, returns nothing, reads and writes no memory, and cannot
panic. The model: it returns. -/
def StandardCrypto.impl : val :=
  λ: <>,
    #()

end code
end crypto.internal.boring.sig

end Perennial
