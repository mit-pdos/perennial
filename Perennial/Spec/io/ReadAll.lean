/-
`io.ReadAll`'s spec.
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

/-- `io.ReadAll(r)` of a reader `r` keeping the contract `S`, `E` (`io.readerOk`, with no
condition on its calls), from `S r0`: reads until `r` returns an error, and returns the bytes
`ys` it delivered, leaving `S (r0 ++ ys)`, with `nil` if that error was `io.EOF` (`eof`, its
value), else the error, with its evidence. The stream is shorter than `2^60` bytes (`S`'s bound):
the model's heap is unbounded, while `ReadAll`'s `int` sizes (`finalSize`, the next buffer's
size) would overflow past `2^63`. It may not return (a reader that never returns an error:
partial correctness). -/
abbrev io.ReadAll.spec : Prop :=
  ∀ (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (r0 : List w8) (eof : GoInterface),
  (∀ r, S r ⊢ ⌜r.length < 2 ^ 60⌝) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ io.readerOk ri (fun _ _ => True) S E ∗
      globalAddr io.EOF ↦□ eof ∗ S r0 }}
    (App (Val (@! io.ReadAll)) (Val #(interface.ok ri)))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      ∃ ys : List w8, sl ↦* ys ∗ S (r0 ++ ys) ∗
        (⌜err = interface.nil⌝ ∗ □ E (r0 ++ ys) eof ∨
          ⌜err ≠ interface.nil ∧ err ≠ eof⌝ ∗ □ E (r0 ++ ys) err) }}

end spec

end Perennial
