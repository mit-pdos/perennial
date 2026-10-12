/-
`encoding/binary.bigEndian.PutUint64`'s spec.
-/
module

public import Perennial.Proof.encoding.binary.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

abbrev encoding.binary.bigEndian.PutUint64.spec : Prop :=
  ∀ (be : bigEndian) (b : GoSlice) (space rem : List w8) (v : w64),
  space.length = 8 →
  {{ (b ↦* (space ++ rem) : IProp GF) }}
    (App (App (Val (be @!! bigEndian.ty @!! go!"PutUint64")) (Val #b)) (Val #v))
  {{ RET #(); b ↦* ((u64Le v).reverse ++ rem) }}

end spec

end Perennial
