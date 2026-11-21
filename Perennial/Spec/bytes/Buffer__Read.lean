/-
`bytes.Buffer.Read`'s spec.
-/
module

public import Perennial.Proof.bytes.BufferBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

/-- `b.Read(p)` of a `*Buffer` `b` holding the unread bytes `bs`: copies the first
`min(len(bs), len(p))` of them, `ys`, into the front of `p` and returns their number, leaving
the rest of `bs` unread; the error is `nil`, or `io.EOF` (`eof`) when the buffer was empty and
`p` was not. -/
abbrev bytes.Buffer.Read.spec : Prop :=
  ∀ (l : Loc) (bs : List w8) (p : GoSlice) (xs : List w8) (eof : GoInterface),
    {{ globalAddr io.EOF ↦□ eof ∗ bytes.ownBuffer (GF := GF) l bs ∗ p ↦* xs }}
      (App (Val (l @!! go.GoType.PointerType bytes.Buffer.ty @!! go!"Read")) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ⌜sint.Z n = (bs.take xs.length).length ∧
          (err = interface.nil ∨ (err = eof ∧ bs = [] ∧ xs ≠ []))⌝ ∗
        p ↦* (bs.take xs.length ++ xs.drop (bs.take xs.length).length) ∗
        bytes.ownBuffer l (bs.drop xs.length) }}

end spec

end Perennial
