/-
`internal.bytealg.HashStrRev`'s spec.
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

/-- `bytealg.HashStrRev[string](sep)`: the Rabin-Karp hash of the reverse of `sep` and
`PrimeRK ^ len(sep)`, mod 2^32. Only the instance at `string` (the one `strings.LastIndex`
calls). -/
abbrev internal.bytealg.HashStrRev.spec : Prop :=
  ∀ (sep : GoString),
    {{ (True : IProp GF) }}
      (App (Val #(functions internal.bytealg.HashStrRev [go.string])) (Val #sep))
    {{ RET (PairV #(internal.bytealg.hashStrRev sep) #(internal.bytealg.powRK sep.length));
        True }}

end spec

end Perennial
