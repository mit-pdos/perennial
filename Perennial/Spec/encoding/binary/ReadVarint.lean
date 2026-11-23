/-
`encoding/binary.ReadVarint`'s spec.
-/
module

public import Perennial.Proof.encoding.binary.Varint
public import Perennial.Proof.io.ByteReader

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

/-- `binary.ReadVarint(r)` (`varint.go:157-164`): `ReadUvarint(r)`'s `ux` and error, and the
`int64` whose zigzag is `ux` (`ux >> 1`, complemented if `ux`'s low bit is set), whatever the
error (`ReadVarint` converts `ux` regardless). -/
abbrev encoding.binary.ReadVarint.spec : Prop :=
  ∀ (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (r0 : List w8) (eof ueof ovf : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
      isPkgInit (PROP := IProp GF) pkg_id.io ∗ io.byteReaderOk ri S E ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      globalAddr errOverflow ↦□ ovf ∗ S r0 }}
    (App (Val (@! ReadVarint)) (Val #(interface.ok ri)))
  {{ (x : w64) (err : GoInterface), RET (PairV #x #err);
      ∃ (V : List w8) (ux : w64), S (r0 ++ V) ∗
        encoding.binary.uvarintRes E eof ueof ovf r0 V ux err ∗
        ⌜x = if ux &&& W64 1 = W64 0 then ux >>> W64 1 else ~~~ (ux >>> W64 1)⌝ }}

end spec

end Perennial
