/-
`internal.bytealg.HashStr`'s spec.
-/
module

public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `bytealg.HashStr(sep)`, at type `string`: the Rabin-Karp hash of `sep` and `PrimeRK` to the
power `len(sep)`. -/
abbrev internal.bytealg.HashStr.spec : Prop :=
  ∀ (sep : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (Val #(functions HashStr [go.string])) (Val #sep))
    {{ RET (PairV #(rkHash sep) #(primeRK ^ sep.length)); True }}

end spec

end Perennial
