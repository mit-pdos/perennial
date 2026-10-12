/-
`github.com/tchajed/marshal.ReadBool`'s spec.
-/
module

public import Perennial.Proof.github_com.tchajed.marshal.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

/-- `ReadBool(s)`: whether the first byte of `s` is non-zero, and the rest. -/
abbrev github_com.tchajed.marshal.ReadBool.spec : Prop :=
  ∀ (s : GoSlice) (q : DFrac) (bit : w8) (tail : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦*{q} (bit :: tail) }}
      (App (Val (@! ReadBool)) (Val #s))
    {{ (b : Bool) (s' : GoSlice), RET (PairV #b #s');
        ⌜b = decide (uint.Z bit ≠ 0)⌝ ∗ s' ↦*{q} tail }}

end spec

end Perennial
