/-
`crypto/sha1.Sum`'s spec.
-/
module

public import Perennial.Proof.crypto.sha1.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha1.Assumptions]

/-- **`Sum(data)` is the SHA-1 digest of `data`** (FIPS 180-4, `crypto.sha1.sha1`), when the run's
`fips140` GODEBUG setting is unset or `off` (`GodebugFips140Off`; in mode `only`, `Sum` panics). -/
abbrev crypto.sha1.Sum.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (data : List w8),
    crypto.fips140.GodebugFips140Off →
    {{ isPkgInit (PROP := IProp GF) pkg_id.crypto.sha1 ∗ s ↦*{dq} data }}
      (App (Val (@! crypto.sha1.Sum)) (Val #s))
    {{ RET #(array.mk 20 (crypto.sha1.sha1 data) : GoArray w8 20); s ↦*{dq} data }}

end spec

end Perennial
