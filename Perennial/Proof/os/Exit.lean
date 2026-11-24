/-
The proof of `os.Exit`.
-/
module

public import Perennial.Spec.os.Exit
public import Perennial.Spec.internal.testlog.PanicOnExit0
public import Perennial.Spec.syscall.Exit

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : os.Assumptions]

theorem os.Exit.wp_proof
    (wp_PanicOnExit0 : internal.testlog.PanicOnExit0.spec (GF := GF) (hG := hG))
    (wp_syscall_Exit : syscall.Exit.spec (GF := GF) (hG := hG)) :
    os.Exit.spec (GF := GF) (hG := hG) := fun code => by
  wp_start
  wp_auto
  wp_bind (If _ _ _)
  wp_if_destruct
  · wp_apply wp_PanicOnExit0 $$ [$Hpkg]
    -- runtime_beforeExit: its trusted model does nothing
    wp_func_call
    wp_call
    wp_auto
    wp_apply wp_syscall_Exit as Hf
    iexfalso
    iexact Hf
  · -- runtime_beforeExit: its trusted model does nothing
    wp_func_call
    wp_call
    wp_auto
    wp_apply wp_syscall_Exit as Hf
    iexfalso
    iexact Hf


end proof

end Perennial
