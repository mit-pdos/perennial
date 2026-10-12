/-
The proof of `github.com/goose-lang/std.(*JoinHandle).finish`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.JoinHandle__finish
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Cond__Signal
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

theorem github_com.goose_lang.std.JoinHandle.finish.wp_proof
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Cond_Signal : sync.Cond.Signal.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.goose_lang.std.JoinHandle.finish.spec (GF := GF) (hG := hG) := fun l P => by
  wp_start as ⟨#Hhandle, HPin⟩
  unfold isJoinHandle
  iNamed Hhandle
  wp_auto
  wp_apply wp_Mutex_Lock $$ [$Hlock] as ⟨locked, Hinv⟩
  iNamed Hinv
  wp_auto
  wp_apply wp_Cond_Signal $$ [$Hcond]
  wp_apply wp_Mutex_Unlock $$ [$Hlock $locked done_b HPin HP]
  · iclear HP
    inext; iexists true; iframe done_b; unfold jhP; simp only [↓reduceIte]; iframe HPin
  wp_end

end proof

end Perennial
