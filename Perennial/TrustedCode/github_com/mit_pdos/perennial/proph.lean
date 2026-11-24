/-
Trusted definitions of `github.com/mit-pdos/perennial/proph`, Perennial's package of
prophecy variables.

The definitions live in the namespace of the generated package
(`github_com.mit_pdos.perennial.proph`), where the generated code refers to them.

`proph.go` declares `NewProph() ProphId`, `(ProphId) ResolveBool(bool)`,
`(ProphId) ResolveU64(uint64)` and `(ProphId) Resolve(any)` as no-op stubs: `NewProph`
returns `ProphId{}`, the resolves have empty bodies. goose translates them, but the
translation is the no-op: the functions exist to carry the meaning of a prophecy
variable, which has no runtime effect and which no Go code can express. So they are
trusted, modelled by GooseLang's prophecy primitives, which touch only ghost state; the
observable behaviour (no effect, a value of `ProphId`) is the stub's.

The first three are `github.com/goose-lang/primitive`'s prophecy functions, with the same
signatures, so their models are primitive's. `Resolve` is new.
-/
module

public import Perennial.TrustedCode.github_com.goose_lang.primitive

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.mit_pdos.perennial.proph
section code
variable [GooseExts] [GoGlobalContext]

/-- `NewProph()` creates a prophecy variable: `primitive.NewProph`'s model. -/
abbrev NewProph.impl : val := github_com.goose_lang.primitive.NewProph.impl

/-- `p.ResolveBool(b)` resolves the prophecy `p` with the value `#b`:
`primitive.ProphId.ResolveBool`'s model. -/
abbrev ProphId.ResolveBool.impl : val := github_com.goose_lang.primitive.ProphId.ResolveBool.impl

/-- `p.ResolveU64(x)` resolves the prophecy `p` with the value `#x`:
`primitive.ProphId.ResolveU64`'s model. -/
abbrev ProphId.ResolveU64.impl : val := github_com.goose_lang.primitive.ProphId.ResolveU64.impl

/-- `p.Resolve(v)` resolves the prophecy `p` with the interface value `v`. -/
def ProphId.Resolve.impl : val := λ: "p" "v", ResolveProph (Var "p") (Var "v")

/-- `ProphId`'s underlying type: `primitive.ProphId`'s, GooseLang's prophecy identifiers. -/
@[reducible] def ProphId.underlying : go.GoType := github_com.goose_lang.primitive.ProphId.underlying

end code

abbrev ProphId := github_com.goose_lang.primitive.ProphId

end github_com.mit_pdos.perennial.proph

end Perennial
