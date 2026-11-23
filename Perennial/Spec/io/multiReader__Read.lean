/-
`(*multiReader).Read`'s spec.
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

/-- `mr.Read(p)` of the `*multiReader` `l` of the readers `cs`, each keeping its contract
(`io.readerOkOut Out`), from the state having delivered `r` (`io.mrState`): it keeps the same
contract (the conclusion is `io.readerOkOut`'s, with `io.mrState` and `io.mrErr`). It reads the
readers in turn, each until it returns `EOF`, passing `p` to each: so `Out` must allow a read
that delivers nothing to be followed by another (`io.OutLaw`). `EOF` (`eof`) only comes once every
reader has returned it; an error other than `EOF` is the current reader's. No reader may be a
`*multiReader`: Go's `Read` takes the readers of a last remaining `*multiReader` in its place
(flattening), reading its fields directly. -/
abbrev io.multiReader.Read.spec : Prop :=
  ∀ (Out : io.ReadOut) (cs : List (io.ReaderC GF)) (eof : GoInterface) (l : Loc) (r : List w8)
    (p : GoSlice) (xs : List w8),
  io.OutLaw Out →
  (∀ c ∈ cs, c.ri.ty ≠ go.GoType.PointerType io.multiReader.ty) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr io.EOF ↦□ eof ∗
      □ (∀ c, ⌜c ∈ cs⌝ -∗ io.readerOkOut Out c.ri c.S c.E) ∗
      io.mrState l cs eof r ∗ p ↦* xs }}
    (App (Val #(methods (go.GoType.PointerType io.multiReader.ty) go!"Read" #l)) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys c : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length ∧ Out xs ys c⌝ ∗
        p ↦* c ∗ io.mrState l cs eof (r ++ ys) ∗ io.errAt (io.mrErr cs eof) (r ++ ys) err ∗
        ⌜io.ptrTyped err⌝ }}

end spec

end Perennial
