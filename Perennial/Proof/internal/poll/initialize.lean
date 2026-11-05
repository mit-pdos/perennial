/-
The proof of `internal.poll.initialize'`: it initializes its imports and runs the variable
initializers; `ErrNoDeadline` is kept with its `errors.New` error (`errors.wp_New_errorString`),
`ErrDeadlineExceeded` with its value.
-/
module

public import Perennial.Spec.internal.poll.initialize
public import Perennial.Spec.internal.syscall.unix.initialize
public import Perennial.Spec.syscall.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.sync.OnceValue
public import Perennial.Spec.errors.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.poll.Assumptions]

open internal.poll in
theorem internal.poll.initialize'.wp_proof
    (wp_unix_initialize : internal.syscall.unix.initialize'.spec (GF := GF) (hG := hG))
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_syscall_initialize : syscall.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG))
    (wp_OnceValue : sync.OnceValue.spec (GF := GF) (hG := hG)) :
    internal.poll.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc as Hsplice
  wp_apply wp_GlobalAlloc as Hhook1
  wp_apply wp_GlobalAlloc as Haccept
  wp_apply wp_GlobalAlloc as Hclose
  wp_apply wp_GlobalAlloc as Haccept4
  wp_apply wp_GlobalAlloc as Hhook2
  wp_apply wp_GlobalAlloc as HNP
  wp_apply wp_GlobalAlloc as HDE
  wp_apply wp_GlobalAlloc as HND
  wp_apply wp_GlobalAlloc as HFC
  wp_apply wp_GlobalAlloc as HNC
  wp_apply wp_GlobalAlloc as HENOENT
  wp_apply wp_GlobalAlloc as HEINVAL
  wp_apply wp_GlobalAlloc as HEAGAIN
  wp_apply wp_GlobalAlloc as Hcfr
  wp_apply wp_errors_initialize _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  wp_apply wp_syscall_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsyscall⟩
  wp_apply wp_sync_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply wp_unix_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hunix⟩
  set_option maxRecDepth 20000 in
  wp_apply wp_OnceValue as %cfr -
  wp_apply errors.wp_New_errorString as %xFC #EFC
  wp_apply errors.wp_New_errorString as %xND #END
  ipersist HND
  wp_alloc_anon
  wp_auto
  ipersist HDE
  wp_apply errors.wp_New_errorString as %xNP #ENP
  ihave #NND : errors.newVar (GF := GF) ErrNoDeadline go!"file type does not support deadline" $$ []
  · iunfold errors.newVar
    iexists _
    iframe HND END
  iframe Hown
  is_pkg_init_finish
  imodintro
  isplitl []
  · iexact NND
  · iexists _
    iexact HDE

end proof

end Perennial
