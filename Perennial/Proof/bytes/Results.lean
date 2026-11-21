/-
Results of `bytes` derived from the linked ones: a `*Buffer` keeps the reader contract
(`bytes.wp_buffer_readerOk`).
-/
module

public import Perennial.Proof.bytes.Link
public import Perennial.Proof.bytes.BufferReader

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

/-- **A `*Buffer` `l` holding `bs` is an `io.Reader` of the stream `bs`**: it keeps the reader
contract (`io.readerOk`) with the state `bytes.bufferReadState l bs` and the errors
`bytes.bufferReadErr bs eof` (`io.EOF`, once all of `bs` is delivered). -/
theorem bytes.wp_buffer_readerOk (l : Loc) (bs : List w8) (eof : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr io.EOF ↦□ eof ⊢
      io.readerOk ⟨go.GoType.PointerType bytes.Buffer.ty, #l⟩ (fun _ _ => True)
        (bytes.bufferReadState l bs) (bytes.bufferReadErr bs eof) :=
  bytes.buffer_readerOk bytes.Buffer.wp_Read l bs eof

end results

end Perennial
