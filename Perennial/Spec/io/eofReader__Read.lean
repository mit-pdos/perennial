/-
`(eofReader).Read`'s spec.
-/
module

public import Perennial.Proof.io.Multi

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

/-- `eofReader{}.Read(p)` (what `multiReader.Read` puts in place of a reader that has returned
`EOF`): `0, EOF`, `eof` being `io.EOF`'s value. -/
abbrev io.eofReader.Read.spec : Prop :=
  ∀ (p : GoSlice) (eof : GoInterface),
  {{ (globalAddr io.EOF ↦□ eof : IProp GF) }}
    (App (Val #(methods io.eofReader.ty go!"Read" #(io.eofReader.mk))) (Val #p))
  {{ RET (PairV #(W64 0) #eof); True }}

end spec

end Perennial
