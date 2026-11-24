/-
`internal.bytealg.HashStr`'s spec.
-/
module

public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `bytealg.HashStr[string](sep)`: the Rabin-Karp hash of `sep` and `PrimeRK ^ len(sep)`, mod
2^32. Only the instance at `string` (the one `IndexRabinKarp[string]` calls). -/
abbrev internal.bytealg.HashStr.spec : Prop :=
  ∀ (sep : GoString),
    {{ (True : IProp GF) }}
      (App (Val #(functions internal.bytealg.HashStr [go.string])) (Val #sep))
    {{ RET (PairV #(internal.bytealg.hashStr sep) #(internal.bytealg.powRK sep.length)); True }}

end spec

end Perennial
