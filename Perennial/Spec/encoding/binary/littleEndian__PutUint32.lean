/-
`encoding/binary.littleEndian.PutUint32`'s spec.
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

abbrev encoding.binary.littleEndian.PutUint32.spec : Prop :=
  ∀ (le : littleEndian) (b : GoSlice) (space rem : List w8) (v : w32),
  space.length = 4 →
  {{ (b ↦* (space ++ rem) : IProp GF) }}
    (App (App (Val (le @!! littleEndian.ty @!! go!"PutUint32")) (Val #b)) (Val #v))
  {{ RET #(); b ↦* (u32Le v ++ rem) }}

end spec

end Perennial
