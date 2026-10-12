/-
`sort.Reverse`'s spec.
-/
module

public import Perennial.Proof.sort.SorterBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

/-- `sort.Reverse(data)` is a sorter of the same list by the converse order. -/
abbrev sort.Reverse.spec : Prop :=
  ∀ {E : Type} (x : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ isSorter x own R }}
      (App (Val (@! Reverse)) (Val #(interface.ok x)))
    {{ (y : GoInterfaceOk), RET #(interface.ok y); isSorter y own (fun a b => R b a) }}

end spec

end Perennial
