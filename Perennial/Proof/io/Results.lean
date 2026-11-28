/-
What is derived from the linked results of `io`: a `*multiReader` is a reader
(`io.multiReader_readerOkOut`), the concatenation of its readers' streams.
-/
module

public import Perennial.Proof.io.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [HasExt reflectExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

/-- **A `*multiReader` `l` of the readers `cs` is a reader** (`io.readerOkOut Out`) with the
state `io.mrState l cs eof` and the errors `io.mrErr cs eof`, if each of `cs` is one (and none is
a `*multiReader`): `io.multiReader.wp_Read` as a contract. With `io.wp_MultiReader`, which gives
its initial state `io.mrState l cs eof []`. -/
theorem io.multiReader_readerOkOut (Out : io.ReadOut) (cs : List (io.ReaderC GF))
    (eof : GoInterface) (l : Loc) (hOut : io.OutLaw Out)
    (hty : ∀ c ∈ cs, c.ri.ty ≠ go.GoType.PointerType io.multiReader.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr io.EOF ↦□ eof ∗
      □ (∀ c, ⌜c ∈ cs⌝ -∗ io.readerOkOut Out c.ri c.S c.E) ⊢
      io.readerOkOut Out ⟨go.GoType.PointerType io.multiReader.ty, #l⟩ (io.mrState l cs eof)
        (io.mrErr cs eof) := by
  iintro ⟨#Hinit, #Heof, #Hrs⟩
  iunfold io.readerOkOut
  imodintro
  iintro %r %p %xs %Φ
  imodintro
  iintro ⟨HS, Hp⟩ HΦ
  iapply io.multiReader.wp_Read Out cs eof l r p xs hOut hty $$ [HS Hp] HΦ
  iframe Hinit Heof Hrs HS Hp

end results

end Perennial
