/-
`encoding/binary.PutUvarint`'s spec.
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

/-- `binary.PutUvarint(buf, x)` (`varint.go:51-60`): writes `uvarintEnc x` into the front of
`buf` and returns its length. Go panics (an index out of range, `varint.go:54` or `:58`) if `buf`
is shorter than the encoding: the precondition. It reads no package variable. -/
abbrev encoding.binary.PutUvarint.spec : Prop :=
  ∀ (buf : GoSlice) (xs : List w8) (x : w64),
  (encoding.binary.uvarintEnc (uint.nat x)).length ≤ xs.length →
  {{ (buf ↦* xs : IProp GF) }}
    (App (App (Val (@! PutUvarint)) (Val #buf)) (Val #x))
  {{ RET #(W64 (encoding.binary.uvarintEnc (uint.nat x)).length);
      buf ↦* (encoding.binary.uvarintEnc (uint.nat x) ++
        xs.drop (encoding.binary.uvarintEnc (uint.nat x)).length) }}

end spec

end Perennial
