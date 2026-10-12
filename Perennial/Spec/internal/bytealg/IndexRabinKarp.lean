/-
`internal.bytealg.IndexRabinKarp`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `bytealg.IndexRabinKarp(s, sep)`, at type `string`, for `len(sep) ≤ len(s)`: the index of the
first occurrence of `sep` in `s`, or `-1`. -/
abbrev internal.bytealg.IndexRabinKarp.spec : Prop :=
  ∀ (s sep : GoString) (Hlen : sep.length ≤ s.length),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (App (Val #(functions IndexRabinKarp [go.string])) (Val #s)) (Val #sep))
    {{ RET #(indexResult s sep); True }}

end spec

end Perennial
