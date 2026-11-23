/-
The proof of `internal.testlog.PanicOnExit0`.
-/
module

public import Perennial.Spec.internal.testlog.PanicOnExit0
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

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
variable [package_sem : internal.testlog.Assumptions]

theorem internal.testlog.PanicOnExit0.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    internal.testlog.PanicOnExit0.spec (GF := GF) (hG := hG) := by
  wp_start
  ihave #Hmu := internal.testlog.isInit_access $$ Hpkg
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply wp_Lock $$ [$Hmu] as ⟨Hlocked, Hval⟩
  wp_apply wp_Unlock $$ [$Hmu $Hlocked $Hval]
  iapply HΦ
  itrivial

end proof

end Perennial
