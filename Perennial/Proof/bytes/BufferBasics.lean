/-
Shared definitions of the proofs of `bytes.Buffer`: `bytes.ownBuffer l bs`, a `*Buffer` whose
unread content is `bs`, and the reader contract (`io.readerOk`) a `*Buffer` keeps when read.
-/
module

public import Perennial.Proof.bytes.Base
public import Perennial.Proof.io.Reader

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace bytes

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

/-- **The `*Buffer` at `l` holds the unread bytes `bs`** (exclusive): its slice `buf` holds
`all`, and its read offset `off` is within it, with `bs = all[off:]` (`bytes.Buffer`'s comment:
"contents are the bytes buf[off : len(buf)]"). For reading only: it does not own `buf`'s spare
capacity, which a write would grow into. -/
def ownBuffer (l : Loc) (bs : List w8) : IProp GF :=
  iprop(∃ (b : Buffer) (all : List w8), l ↦ b ∗ b.buf' ↦* all ∗
    ⌜0 ≤ sint.Z b.off' ∧ sint.nat b.off' ≤ all.length ∧ bs = all.drop (sint.nat b.off')⌝)

/-- The state of a `*Buffer` `l` read as a stream of `bs` (`io.readerOk`'s `S`): having
delivered `r`, a prefix of `bs`, it holds the rest. -/
def bufferReadState (l : Loc) (bs : List w8) (r : List w8) : IProp GF :=
  iprop(⌜r <+: bs⌝ ∗ ownBuffer l (bs.drop r.length))

/-- What an error of a `*Buffer` read as a stream of `bs` says (`io.readerOk`'s `E`): it is
`io.EOF` (`eof`), returned only once all of `bs` has been delivered. -/
def bufferReadErr (bs : List w8) (eof : GoInterface) (r : List w8) (e : GoInterface) : IProp GF :=
  iprop(⌜r = bs ∧ e = eof⌝)

end defs

end bytes

end Perennial
