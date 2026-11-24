/-
**An `io.ByteReader` and its contract** (`io/io.go`: "ReadByte reads and returns the next byte
from the input or any error encountered. If ReadByte returns an error, no input byte was
consumed, and the returned byte value is undefined."), the vocabulary of the specs of
`encoding/binary.ReadUvarint` and `ReadVarint`.

* `io.byteReaderOk ri S E` (persistent): `ri.ReadByte()`, from the state `S r` (`r` the bytes
  it has delivered so far), either returns the next byte `c` and `nil`, leaving `S (r ++ [c])`,
  or returns an error with the evidence `E r err` gives of it, a well-typed one
  (`io.ptrTyped`), leaving `S r`. As for `io.readerOk`, the client chooses `S` (what the bytes
  are) and `E` (what an error means there: `io.EOF` only at the end, ...).
-/
module

public import Perennial.Proof.io.Reader

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace io

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`ri` reads bytes by the contract `S`, `E`** (see the file header). -/
def byteReaderOk (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) : IProp GF :=
  iprop(□ ∀ (r : List w8),
    {{ S r }}
      (App (Val #(methods ri.ty go!"ReadByte" ri.v)) (Val #()))
    {{ (c : w8) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ S (r ++ [c])) ∨
        (⌜err ≠ interface.nil⌝ ∗ □ E r err ∗ ⌜ptrTyped err⌝ ∗ S r) }})

instance byteReaderOk_persistent (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) : Persistent (byteReaderOk ri S E) := by
  unfold byteReaderOk; infer_instance

/-- A call of `ReadByte`, with `byteReaderOk` kept folded in the caller's context. -/
theorem wp_byteReader_ReadByte (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r : List w8) :
    {{ byteReaderOk ri S E ∗ S r }}
      (App (Val #(methods ri.ty go!"ReadByte" ri.v)) (Val #()))
    {{ (c : w8) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ S (r ++ [c])) ∨
        (⌜err ≠ interface.nil⌝ ∗ □ E r err ∗ ⌜ptrTyped err⌝ ∗ S r) }} := by
  iintro %Φ ⟨#Hr, HS⟩ HΦ
  unfold byteReaderOk
  iapply Hr $$ %r [HS] HΦ
  iexact HS

end defs

end io

end Perennial
