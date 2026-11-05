/-
The proof of `internal.syscall.unix.initialize'`: it initializes `syscall` and stores a function
value.
-/
module

public import Perennial.Spec.internal.syscall.unix.initialize
public import Perennial.Spec.syscall.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.syscall.unix.Assumptions]

open internal.syscall.unix in
theorem internal.syscall.unix.initialize'.wp_proof
    (wp_syscall_initialize : syscall.initialize'.spec (GF := GF) (hG := hG)) :
    internal.syscall.unix.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (wp_apply wp_GlobalAlloc as _)
  wp_apply wp_syscall_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hsyscall⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
