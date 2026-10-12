/-
`StringToByteSlice`'s spec (`goose/model/strings/convert.go`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : go.StringSemantics]

abbrev github_com.mit_pdos.perennial.goose.model.strings.StringToByteSlice.spec : Prop :=
  ∀ {s : Stuckness} {E : CoPset} (str : GoString),
    {{ (True : IProp GF) }}
      (App (Val (@! StringToByteSlice)) (Val #str)) @ s; E
    {{ (sl : GoSlice), RET #sl; sl ↦* str ∗ ownSliceCap w8 sl (DFrac.own 1) }}

end spec

end Perennial
