/-
`ByteSliceToString`'s spec (`goose/model/strings/convert.go`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : go.StringSemantics]

abbrev github_com.mit_pdos.perennial.goose.model.strings.ByteSliceToString.spec : Prop :=
  ∀ {s : Stuckness} {E : CoPset} (sl : GoSlice) (str : List w8) (dq : DFrac),
    {{ (sl ↦*{dq} str : IProp GF) }}
      (App (Val (@! ByteSliceToString)) (Val #sl)) @ s; E
    {{ RET #str; sl ↦*{dq} str }}

end spec

end Perennial
