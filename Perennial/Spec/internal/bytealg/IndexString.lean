/-
`internal.bytealg.IndexString`'s spec.
-/
module

public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `bytealg.IndexString(a, b)`, for `2 ≤ len(b) ≤ MaxLen`: the index of the first occurrence of
`b` in `a`, or `-1`. -/
abbrev internal.bytealg.IndexString.spec : Prop :=
  ∀ (a b : GoString) (m : w64) (Hb : 2 ≤ b.length ∧ b.length ≤ sint.Z m),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg ∗
        typedPointsto (globalAddr MaxLen) m DFrac.discard }}
      (App (App (Val (@! IndexString)) (Val #a)) (Val #b))
    {{ RET #(indexResult a b); True }}

end spec

end Perennial
