/-
`slices.nextPowerOfTwo`'s spec.
-/
module

public import Perennial.Proof.slices.PartitionBasics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

/-- `nextPowerOfTwo(length)` is a power of two in `(length, 2 * length]`. -/
abbrev slices.nextPowerOfTwo.spec : Prop :=
  ∀ (length : w64) (h : 0 < sint.Z length),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices }}
      (App (Val (@! nextPowerOfTwo)) (Val #length))
    {{ (m : w64), RET #m; ⌜sint.Z length < uint.Z m ∧ uint.Z m ≤ 2 * sint.Z length⌝ }}

end spec

end Perennial
