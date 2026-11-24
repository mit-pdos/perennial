/-
The proof of `internal/sync.(*Mutex).Unlock`.
-/
module
public import Perennial.Spec.internal.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.sync.Assumptions]

theorem internal.sync.Mutex.Unlock.wp_proof
    (wp_CompareAndSwapInt32 : sync.atomic.CompareAndSwapInt32.spec (GF := GF) (hG := hG)) :
    internal.sync.Mutex.Unlock.spec (GF := GF) (hG := hG) := by
  intro m R
  wp_start as ⟨#His, Hown, HR⟩
  simp only [internal.sync.mutexLocked]
  rw [isLock_unseal] at *; unfold isLockDef
  rw [ownLock_unseal]; unfold ownLockDef
  iNamed His
  wp_auto
  wp_apply_core wp_CompareAndSwapInt32 $$ [] [-]
  · iPkgInit
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%v, >Hs, Hrest⟩
  icombine Hs Hown gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  ihave Hfull := (typedPointsto_quarter_three_quarter _ (W32 1)).2 $$ [Hs Hown]
  · iframe
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists (W32 1), (DFrac.own 1)
  iframe Hfull
  isplitr
  · ipureintro; rfl
  iintro Hs
  simp only [↓reduceIte]
  icases (typedPointsto_quarter_three_quarter _ (W32 0)).1 $$ Hs with ⟨Hl1, Hl2⟩
  imod Hmask with _
  imod Hclose $$ [Hl1 Hl2 HR] with _
  · inext; iexists (W32 0); simp only [↓reduceIte]; iframe
  imodintro
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
