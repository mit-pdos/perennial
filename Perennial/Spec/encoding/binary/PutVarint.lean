/-
`encoding/binary.PutVarint`'s spec.
-/
module

public import Perennial.Proof.encoding.binary.Varint

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

/-- `binary.PutVarint(buf, x)` (`varint.go:101-107`): `PutUvarint` of the zigzag of the `int64`
`x` (`2x` for `x ≥ 0`, `-2x - 1` for `x < 0`). Go panics if `buf` is shorter than the encoding:
the precondition. -/
abbrev encoding.binary.PutVarint.spec : Prop :=
  ∀ (buf : GoSlice) (xs : List w8) (x : w64),
  (encoding.binary.uvarintEnc (encoding.binary.zigzag (sint.Z x))).length ≤ xs.length →
  {{ (buf ↦* xs : IProp GF) }}
    (App (App (Val (@! PutVarint)) (Val #buf)) (Val #x))
  {{ RET #(W64 (encoding.binary.uvarintEnc (encoding.binary.zigzag (sint.Z x))).length);
      buf ↦* (encoding.binary.uvarintEnc (encoding.binary.zigzag (sint.Z x)) ++
        xs.drop (encoding.binary.uvarintEnc (encoding.binary.zigzag (sint.Z x))).length) }}

end spec

end Perennial
