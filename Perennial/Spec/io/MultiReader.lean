/-
`io.MultiReader`'s spec.
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

/-- `io.MultiReader(readers...)` of the readers `cs` (`sl`, read only): a fresh `*multiReader`
`l` (as an `io.Reader`) holding a copy of the slice, in its initial state (`io.mrState`, nothing
delivered), given the readers' initial states. Read with `io.multiReader.Read.spec`. -/
abbrev io.MultiReader.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (cs : List (io.ReaderC GF)) (eof : GoInterface),
  {{ sl ↦*{dq} cs.map io.ReaderC.iface ∗ [∗list] c ∈ cs, c.S [] }}
    (App (Val (@! io.MultiReader)) (Val #sl))
  {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType io.multiReader.ty) #l);
      sl ↦*{dq} cs.map io.ReaderC.iface ∗ io.mrState l cs eof [] }}

end spec

end Perennial
