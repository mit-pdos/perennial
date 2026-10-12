/-
`strings.Split`'s spec.
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

/-- `strings.Split(s, sep)`, for a non-empty `sep` and `s` shorter than `2^63 - 1` bytes: a new
slice of the fields `split s sep`. (For an empty `sep` Go splits `s` into its UTF-8 sequences,
which this spec does not cover.) -/
abbrev strings.Split.spec : Prop :=
  ∀ (s sep : GoString) (Hsep : sep ≠ []) (Hs : s.length < 2 ^ 63 - 1),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! Split)) (Val #s)) (Val #sep))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* split s sep ∗ ownSliceCap GoString sl (DFrac.own 1) }}

end spec

end Perennial
