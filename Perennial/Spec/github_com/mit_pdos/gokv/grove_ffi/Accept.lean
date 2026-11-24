/-
`github.com/mit-pdos/gokv/grove_ffi.Accept`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.gokv.grove_ffi.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std grove_ext

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt groveExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.gokv.grove_ffi.Assumptions]

/-- `Accept(l)`: a connection from the listener's endpoint to some remote endpoint. -/
abbrev github_com.mit_pdos.gokv.grove_ffi.Accept.spec : Prop :=
  ∀ (l : Loc) (c_l : Endpoint),
    {{ isListener (GF := GF) l c_l }}
      (App (Val (@! Accept)) (Val #l))
    {{ (c : Loc) (c_r : Endpoint), RET #c; isConnection c c_l c_r }}

end spec

end Perennial
