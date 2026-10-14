/-
`github.com/tchajed/marshal.ReadLenPrefixedBytes`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

/-- `ReadLenPrefixedBytes(s)`: reads a little-endian length `len`, then that many bytes. -/
abbrev github_com.tchajed.marshal.ReadLenPrefixedBytes.spec : Prop :=
  ∀ (s : GoSlice) (q : DFrac) (len : w64) (head tail : List w8),
  head.length = uint.nat len →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗
        s ↦*{q} (u64Le len ++ head ++ tail) }}
      (App (Val (@! ReadLenPrefixedBytes)) (Val #s))
    {{ (b s' : GoSlice), RET (PairV #b #s'); b ↦*{q} head ∗ s' ↦*{q} tail }}

end spec

end Perennial
