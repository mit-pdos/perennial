/-
`crypto/sha1.(*digest).checkSum`'s spec.
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

/-- `d.checkSum()` of a digest that has absorbed `m` pads `m` (FIPS 180-4 §5.1.1) and returns its SHA-1 digest, when the `fips140` setting is not `only` (in mode `only` it panics). -/
abbrev crypto.sha1.digest.checkSum.spec : Prop :=
  ∀ (d : Loc) (v : crypto.sha1.digest) (m : List w8),
    crypto.fips140.GodebugFips140Off →
    crypto.sha1.absorbed v m →
    {{ isPkgInit (PROP := IProp GF) pkg_id.crypto.sha1 ∗ d ↦ v }}
      (App (Val (d @!! go.GoType.PointerType crypto.sha1.digest.ty @!! go!"checkSum")) (Val #()))
    {{ RET #(array.mk 20 (crypto.sha1.sha1 m) : GoArray w8 20); ∃ v' : crypto.sha1.digest, d ↦ v' }}

end spec

end Perennial
