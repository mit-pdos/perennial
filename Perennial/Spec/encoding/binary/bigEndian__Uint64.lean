/-
`encoding/binary.bigEndian.Uint64`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

abbrev encoding.binary.bigEndian.Uint64.spec : Prop :=
  ∀ (be : bigEndian) (b : GoSlice) (bs rem : List w8) (dq : DFrac),
  bs.length = 8 →
  {{ (b ↦*{dq} (bs ++ rem) : IProp GF) }}
    (App (Val (be @!! bigEndian.ty @!! go!"Uint64")) (Val #b))
  {{ RET #(leToU64 bs.reverse); b ↦*{dq} (bs ++ rem) }}

end spec

end Perennial
