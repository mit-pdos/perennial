/-
`encoding/binary.ReadUvarint`'s spec.
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

/-- `binary.ReadUvarint(r)` (`varint.go:130-151`) of a byte reader `r` keeping the contract `S`,
`E` (`io.byteReaderOk`), from `S r0`: reads the bytes `V`, one `ReadByte` each, leaves
`S (r0 ++ V)`, and returns a value and an error as `encoding.binary.uvarintRes` says (`eof`,
`ueof`, `ovf`: the values of `io.EOF`, `io.ErrUnexpectedEOF` and `errOverflow`): a varint it
accepts and its value; the overflow of ten bytes and `errOverflow`; or the reader's error, but
`ErrUnexpectedEOF` in place of `EOF` after some bytes. -/
abbrev encoding.binary.ReadUvarint.spec : Prop :=
  ∀ (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (r0 : List w8) (eof ueof ovf : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
      isPkgInit (PROP := IProp GF) pkg_id.io ∗ io.byteReaderOk ri S E ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      globalAddr errOverflow ↦□ ovf ∗ S r0 }}
    (App (Val (@! ReadUvarint)) (Val #(interface.ok ri)))
  {{ (x : w64) (err : GoInterface), RET (PairV #x #err);
      ∃ V : List w8, S (r0 ++ V) ∗ encoding.binary.uvarintRes E eof ueof ovf r0 V x err }}

end spec

end Perennial
