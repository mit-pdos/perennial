/-
`io.ReadFull`'s spec.
-/
module

public import Perennial.Proof.io.Reader

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

/-- `io.ReadFull(r, buf)` of a reader `r` keeping the contract `Pre`, `S`, `E`
(`io.readerOk`), from `S r0`: delivers `ys` into the front of `buf` and leaves `S (r0 ++ ys)`,
returning `len(ys)` and an error as `io.readFullRes` says (`nil` when all came; else the
reader's last error with its evidence, or `io.ErrUnexpectedEOF` for an `io.EOF` after some
bytes; `eof`, `ueof`: the values of `io.EOF`, `io.ErrUnexpectedEOF`). Each `Read` is of `buf`'s
remaining bytes, never empty (the loop reads only while some are left), so `Pre` must hold of every
such call. It may not return (a reader that keeps
returning `0, nil`: partial correctness). -/
abbrev io.ReadFull.spec : Prop :=
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r0 : List w8) (p : GoSlice) (xs : List w8)
    (eof ueof : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ io.readerOk ri Pre S E ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      ⌜∀ ys : List w8, ys.length < xs.length → Pre (r0 ++ ys) (xs.length - ys.length)⌝ ∗
      S r0 ∗ p ↦* xs }}
    (App (App (Val (@! io.ReadFull)) (Val #(interface.ok ri))) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ S (r0 ++ ys) ∗
        io.readFullRes E eof ueof r0 ys xs.length err }}

end spec

end Perennial
