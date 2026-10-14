/-
`sort.xorshift.Next`'s spec.
-/
module

public import Perennial.Proof.sort.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

abbrev sort.xorshift.Next.spec : Prop :=
  ∀ (r : Loc) (v : xorshift),
    {{ (r ↦ v : IProp GF) }}
      (App (Val (r @!! go.GoType.PointerType xorshift.ty @!! go!"Next")) (Val #()))
    {{ (v' : xorshift) (n : w64), RET #n; r ↦ v' }}

end spec

end Perennial
