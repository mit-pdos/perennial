/-
`github.com/tchajed/marshal.WriteInt32`'s spec.
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

/-- `WriteInt32(s, x)`: `s` with the little-endian encoding of `x` appended. The hypothesis
`length vs + 4 ≤ 2^47` is inherited from `reserve.spec` (tight for the same reason). -/
abbrev github_com.tchajed.marshal.WriteInt32.spec : Prop :=
  ∀ (s : GoSlice) (x : w32) (vs : List w8),
  (vs.length : Int) + 4 ≤ 2 ^ 47 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦* vs ∗
        ownSliceCap w8 s (DFrac.own 1) }}
      (App (App (Val (@! WriteInt32)) (Val #s)) (Val #x))
    {{ (s' : GoSlice), RET #s'; s' ↦* (vs ++ u32Le x) ∗ ownSliceCap w8 s' (DFrac.own 1) }}

end spec

end Perennial
