/-
Trusted code for the Go `crypto/rand` package, in namespace `crypto.rand` (as the
generated package).
-/
module

public import Perennial.Golang.Defn
public import Perennial.Code.math.big
public import Perennial.Code.io

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial
noncomputable section

namespace crypto.rand
section code
variable [FfiSyntax] [GoGlobalContext]

/-- `Int(rand, max)`: a uniform random value in `[0, max)`, read from `rand`; Go panics if
`max <= 0`. The model returns an arbitrary value in `[0, max)` (`ArbitraryInt % max`; the
distribution is not modelled) and a `nil` error, for `max` in `[1, 2^63)`; it reads `max`'s
representation (a sign and one magnitude word) directly, and panics outside that range,
as Go does for `max <= 0` (for `max >= 2^63` Go returns a value; the model does not cover
it, and a proof cannot get past the panic).

It does not read `rand`. Go returns `rand`'s read error, if any; the package's own
`Reader` never returns one (since Go 1.24 a failing system RNG crashes the program), and
`wp_Int` (`Perennial/Spec/crypto/rand/Int.lean`) is stated only for that reader. -/
noncomputable def Int.impl : val :=
  λ: "rand" "max",
    let: "abs" := ![math.big.nat.ty] (StructFieldRef math.big.Int'.ty go!"abs" "max") in
    if: (![go.bool] (StructFieldRef math.big.Int'.ty go!"neg" "max")) ||
        (FuncResolve go.len [math.big.nat.ty] #() "abs" ≠⟨go.int⟩ #(W64 1))
    then Panic "crypto/rand: Int is modelled only for 0 < max < 2^63"
    else
      let: "m" := Convert math.big.Word.ty go.uint64
        (![math.big.Word.ty] (IndexRef math.big.nat.ty ("abs", #(W64 0)))) in
      if: ("m" =⟨go.uint64⟩ #(W64 0)) || ("m" ≥⟨go.uint64⟩ #(W64 (2 ^ 63)))
      then Panic "crypto/rand: Int is modelled only for 0 < max < 2^63"
      else
        (FuncResolve math.big.NewInt [] #() (ArbitraryInt %⟨go.uint64⟩ "m"), #interface.nil)

/-- The type of `Reader`'s initial value, `crypto/internal/rand`'s unexported `reader`
(`type reader struct{ drbg.DefaultReader }`, with a `Read` method). `crypto/internal/rand` is
not translated, so nothing gives this type's underlying type or methods. -/
def internalReader.ty : go.GoType :=
  go.GoType.Named go!"crypto/internal/rand.reader" []

/-- The initializer of `Reader` (`crypto/rand/rand.go`):

```go
var Reader io.Reader = rand.Reader // crypto/internal/rand: var Reader io.Reader = reader{}
```

The model allocates `Reader` (an `io.Reader`, named by its string as goose names it, since
this file comes before the generated code) and stores an interface value whose dynamic type
is the one Go stores, `crypto/internal/rand.reader`, with `#()` in place of the `reader{}`
value. `crypto/internal/rand` is not translated: goose translates `Reader`'s initializer as a
load of `crypto/internal/rand.Reader`, but that package's `reader` embeds
`crypto/internal/fips140/drbg.DefaultReader`, and `drbg`'s initialization runs the DRBG's
FIPS self-test. Go's initializer only copies an interface value, so it cannot panic and has no
other effect.

The stored value cannot be told apart from Go's by a proof: it is non-nil and of the right
dynamic type, as in Go (a nil check or a type switch sees what Go sees). Every operation that
would inspect the `#()` (calling `Read`, comparing two such values) needs `reader`'s underlying
type or methods, which nothing gives, so a proof cannot step it; asserting it to a non-empty
interface type steps, but to an outcome fixed by the unspecified `methodSet`, which a proof
cannot rely on either way. `Int` above does not read its reader. -/
def Reader.init : val :=
  λ: <>,
    go.GlobalAlloc go!"crypto/rand.Reader" io.Reader.ty #() ;;
    GlobalVarAddr go!"crypto/rand.Reader" #() <-[io.Reader.ty]
      #(interface.mkOk internalReader.ty #())

end code
end crypto.rand

end

end Perennial
