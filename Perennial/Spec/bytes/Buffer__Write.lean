/-
`bytes.Buffer.Write`'s spec.
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

/-- `b.Write(p)` of a `*Buffer` holding the unread bytes `bs`: appends `p`'s bytes `d` (growing the
buffer as needed; it only reads `p`) and returns `len(p), nil`. Go's `Write` panics with
`ErrTooLarge` only when the buffer cannot grow, which an owned buffer's size excludes. -/
abbrev bytes.Buffer.Write.spec : Prop :=
  ∀ (l : Loc) (bs : List w8) (p : GoSlice) (dq : DFrac) (d : List w8),
    {{ bytes.ownBuffer (GF := GF) l bs ∗ p ↦*{dq} d }}
      (App (Val (l @!! go.GoType.PointerType bytes.Buffer.ty @!! go!"Write")) (Val #p))
    {{ RET (PairV #(W64 (d.length : Int)) #interface.nil);
        bytes.ownBuffer l (bs ++ d) ∗ p ↦*{dq} d }}

end spec

end Perennial
