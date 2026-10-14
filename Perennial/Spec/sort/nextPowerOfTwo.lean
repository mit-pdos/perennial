/-
`sort.nextPowerOfTwo`'s spec.
-/
module

public import Perennial.Proof.sort.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

abbrev sort.nextPowerOfTwo.spec : Prop :=
  ∀ (length : w64),
    0 < sint.Z length →
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort }}
      (App (Val (@! nextPowerOfTwo)) (Val #length))
    {{ (m : w64), RET #m; ⌜sint.Z length < uint.Z m ∧ uint.Z m ≤ 2 * sint.Z length⌝ }}

end spec

end Perennial
