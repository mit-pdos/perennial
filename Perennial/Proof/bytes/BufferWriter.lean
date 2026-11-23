/-
A `*bytes.Buffer` as the `io.Writer` of `fmt.Fprintf` (`fmt.writeSpec`).
-/
module

public import Perennial.Spec.bytes.Buffer__Write
public import Perennial.Proof.fmt.Args

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

/-- **A `*Buffer` holding `bs` is a writer for `fmt.Fprintf`**: its `Write` of the bytes `s`
appends them (`bytes.Buffer.Write.spec`) and returns `len(s), nil`. -/
theorem bytes.Buffer.writeSpec (hWrite : bytes.Buffer.Write.spec (GF := GF) (hG := hG))
    (l : Loc) (bs : List w8) :
    ⊢ fmt.writeSpec (GF := GF) ⟨go.GoType.PointerType bytes.Buffer.ty, #l⟩ (bytes.ownBuffer l bs)
      (fun s n err => iprop(⌜n = W64 (s.length : Int) ∧ err = interface.nil⌝ ∗
        bytes.ownBuffer l (bs ++ s))) := by
  unfold fmt.writeSpec
  iintro %sl %s %Φ HP Hsl HΦ
  iapply hWrite l bs sl (DFrac.own 1) s $$ [$HP $Hsl]
  inext
  iintro ⟨HP, Hsl⟩
  iapply HΦ $$ Hsl
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iexact HP

end proof

end Perennial
