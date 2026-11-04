/-
Specs of the trusted models of `os` (`Perennial/TrustedCode/os.lean`) that `os`'s initializer
runs: `runtime_args` (an arbitrary `[]string`), and the standard streams' initializers (`Stdin`,
`Stdout`: nothing; `Stderr`: the variable holds some pointer). `os`'s initializer is proved by
its clients (it is names-only here but for its initializers).
-/
module

public import Perennial.Proof.syscall.initialize
public import Perennial.Code.os

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace os

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The model of `runtime_args` returns some slice of strings, owned with its capacity. -/
theorem wp_runtime_args_impl :
    {{ (True : IProp GF) }}
      (App (Val runtime_args.impl) (Val #()))
    {{ (s : GoSlice), RET #s; ∃ xs : List GoString,
        s ↦* xs ∗ ownSliceCap GoString s (DFrac.own 1) }} :=
  syscall.wp_arbitraryStrings

/-- `Stdin`'s initializer (the model) does nothing. -/
theorem wp_Stdin_init :
    {{ (True : IProp GF) }} (App (Val Stdin.init) (Val #())) {{ RET #(); True }} := by
  wp_start
  unfold Stdin.init
  wp_auto
  iapply HΦ; itrivial

/-- `Stdout`'s initializer (the model) does nothing. -/
theorem wp_Stdout_init :
    {{ (True : IProp GF) }} (App (Val Stdout.init) (Val #())) {{ RET #(); True }} := by
  wp_start
  unfold Stdout.init
  wp_auto
  iapply HΦ; itrivial

/-- `Stderr`'s initializer (the model) allocates the variable and stores some pointer. -/
theorem wp_Stderr_init :
    {{ (True : IProp GF) }} (App (Val Stderr.init) (Val #()))
    {{ RET #(); ∃ f : Loc, globalAddr Stderr ↦ f }} := by
  wp_start
  unfold Stderr.init
  wp_auto
  wp_apply wp_GlobalAlloc (V := Loc) go!"os.Stderr"
    (go.GoType.PointerType (go.GoType.Named go!"os.File" [])) as HS
  wp_auto
  wp_apply wp_alloc_untyped as %l -
  wp_auto
  iapply HΦ
  iexists _
  iexact HS

end wps

end os

end Perennial
