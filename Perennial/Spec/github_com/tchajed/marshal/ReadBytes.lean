/-
`github.com/tchajed/marshal.ReadBytes`'s spec.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

/-- `ReadBytes(s, len)`: splits `s` into its first `len` bytes and the rest (sharing `s`). -/
abbrev github_com.tchajed.marshal.ReadBytes.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (len : w64) (head tail : List w8),
  head.length = uint.nat len →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦*{dq} (head ++ tail) }}
      (App (App (Val (@! ReadBytes)) (Val #s)) (Val #len))
    {{ (b s' : GoSlice), RET (PairV #b #s'); b ↦*{dq} head ∗ s' ↦*{dq} tail }}

end spec

end Perennial
