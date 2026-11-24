/-
`github.com/mit-pdos/gokv/grove_ffi.Connect`'s spec.
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

/-- `Connect(remote)`: either an error (`Err` set, `Connection` nil) or a new connection to
`remote` from a fresh local endpoint `c_l`, whose channel is empty. -/
abbrev github_com.mit_pdos.gokv.grove_ffi.Connect.spec : Prop :=
  ∀ (c_r : Endpoint),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.gokv.grove_ffi }}
      (App (Val (@! Connect)) (Val #c_r))
    {{ (err : Bool) (c : Loc), RET #(ConnectRet.mk err c);
        if err then ⌜c = null⌝ else ∃ c_l : Endpoint, isConnection c c_l c_r ∗ c_l c↦ ∅ }}

end spec

end Perennial
