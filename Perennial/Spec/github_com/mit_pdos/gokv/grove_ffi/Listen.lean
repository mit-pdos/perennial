/-
`github.com/mit-pdos/gokv/grove_ffi.Listen`'s spec.
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

/-- `Listen(host)`, for a `host` it accepts, not yet listened on: a `Listener` on `host`, which is
now listened on. -/
abbrev github_com.mit_pdos.gokv.grove_ffi.Listen.spec : Prop :=
  ∀ (host : Endpoint), ListenEndpoint host →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.gokv.grove_ffi ∗ host l↦ false }}
      (App (Val (@! Listen)) (Val #host))
    {{ (l : Loc), RET #l; isListener l host ∗ host l↦ true }}

end spec

end Perennial
