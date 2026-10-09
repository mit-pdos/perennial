/-
Trusted code for the Go `crypto/rand` package, in namespace `crypto.rand` (as the
generated package).
-/
module

public import Perennial.Golang.Defn
public import Perennial.Code.math.big

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

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
`wp_Int` (`Perennial/Proof/crypto/rand.lean`) is stated only for that reader. -/
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

end code
end crypto.rand

end Perennial
