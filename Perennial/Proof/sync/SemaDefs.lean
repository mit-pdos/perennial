/-
The runtime semaphore used by `sync`: its invariant (`isSema`) and value (`ownSema`).
The specs of the semaphore functions (`runtime_Semacquire`, ...) are in `Perennial/Spec/sync/`.
-/
module

public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace sync

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The semaphore invariant. -/
abbrev semaInv (x : Loc) (γ : GName) : IProp GF :=
  iprop(∃ v : w32, x ↦ v ∗ ghostVar γ (1 : Qp).half v)

def isSemaDef (x : Loc) (γ : GName) (N : Namespace) : IProp GF :=
  iprop(inv N (semaInv x γ) ∗ ⌜x ≠ null⌝)
@[irreducible] def isSema (x : Loc) (γ : GName) (N : Namespace) : IProp GF := isSemaDef x γ N
theorem isSema_unseal : @isSema = @isSemaDef := by funext; with_unfolding_all rfl

/-- A semaphore's address is not `null`, nor is any address with the same base
(`LocNonNullFrom`; used by `wp_auto` for field references, `HypPure`). -/
instance isSema_hypPure (x l : Loc) (γ : GName) (N : Namespace) [h : LocNonNullFrom x l] :
    HypPure (isSema (GF := GF) x γ N) (l ≠ null) where
  hyp_pure := by
    rw [isSema_unseal]; unfold isSemaDef
    iintro ⟨_, %Hnn⟩
    ipureintro; exact h.ne_null Hnn

instance isSema_persistent (x : Loc) (γ : GName) (N : Namespace) :
    Persistent (isSema (GF := GF) x γ N) := by
  rw [isSema_unseal]; unfold isSemaDef; infer_instance

def ownSemaDef (γ : GName) (v : w32) : IProp GF := ghostVar γ (1 : Qp).half v
@[irreducible] def ownSema (γ : GName) (v : w32) : IProp GF := ownSemaDef γ v
theorem ownSema_unseal : @ownSema = @ownSemaDef := by funext; with_unfolding_all rfl

instance ownSema_timeless (γ : GName) (v : w32) : Timeless (ownSema (GF := GF) γ v) := by
  rw [ownSema_unseal]; unfold ownSemaDef; infer_instance

theorem init_sema {E : CoPset} (N : Namespace) (sema : Loc) (v : w32) :
    ⊢ typedPointsto (GF := GF) sema v (DFrac.own 1) ={E}=∗
      ∃ γ, isSema sema γ N ∗ ownSema γ v := by
  iintro Hs
  icases typedPointsto_not_null_dup _ _ _ $$ Hs with ⟨Hs, %Hnn⟩
  imod ghostVar_alloc v with ⟨%γ, Hv⟩
  icases ghostVar_split γ v (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
  · rw [Qp.half_add_half]; iexact Hv
  imod inv_alloc N E (semaInv sema γ) $$ [Hs Hv1] with #Hinv
  · inext; iexists v; iframe
  imodintro
  iexists γ
  simp only [isSema_unseal, isSemaDef, ownSema_unseal, ownSemaDef]
  iframe # ∗
  ipureintro; exact Hnn

end wps

end sync

end Perennial
