/-
`strings.genSplit`'s spec.
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `strings.genSplit(s, sep, 0, -1)` (`Split`'s case of `genSplit`, which keeps no part of the
separator and splits at every occurrence), for a non-empty `sep`: a new slice of the fields
`split s sep`. -/
abbrev strings.genSplit.spec : Prop :=
  ∀ (s sep : GoString) (Hsep : sep ≠ []) (Hs : s.length < 2 ^ 63 - 1),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (App (App (Val (@! genSplit)) (Val #s)) (Val #sep)) (Val #(W64 0)))
        (Val #(W64 (-1))))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* split s sep ∗ ownSliceCap GoString sl (DFrac.own 1) }}

end spec

end Perennial
