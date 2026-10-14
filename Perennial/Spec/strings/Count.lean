/-
`strings.Count`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `strings.Count(s, sep)`, for a non-empty `sep`: the number of non-overlapping occurrences of
`sep` in `s`. (For an empty `sep` Go counts the UTF-8 sequences of `s`, plus one, with
`unicode/utf8.RuneCountInString`, which goose does not translate.) -/
abbrev strings.Count.spec : Prop :=
  ∀ (s sep : GoString) (Hsep : sep ≠ []) (Hs : s.length < 2 ^ 63),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! Count)) (Val #s)) (Val #sep))
    {{ RET #(W64 (countOcc s sep)); True }}

end spec

end Perennial
