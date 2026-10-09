/-
The runtime semaphore used by `sync`.
-/
module

public import Perennial.Proof.sync_proof.base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace sync

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The semaphore invariant. -/
abbrev semaInv (x : Loc) (γ : GName) : IProp GF :=
  iprop(∃ v : w32, x ↦ v ∗ ghostVar γ (1 : Qp).half v)

def isSemaDef (x : Loc) (γ : GName) (N : Namespace) : IProp GF := inv N (semaInv x γ)
@[irreducible] def isSema (x : Loc) (γ : GName) (N : Namespace) : IProp GF := isSemaDef x γ N
theorem isSema_unseal : @isSema = @isSemaDef := by funext; with_unfolding_all rfl

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
  imod ghostVar_alloc v with ⟨%γ, Hv⟩
  icases ghostVar_split γ v (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
  · rw [Qp.half_add_half]; iexact Hv
  imod inv_alloc N E (semaInv sema γ) $$ [Hs Hv1] with #Hinv
  · inext; iexists v; iframe
  imodintro
  iexists γ
  simp only [isSema_unseal, isSemaDef, ownSema_unseal, ownSemaDef]
  iframe # ∗

theorem wp_runtime_Semacquire (sema : Loc) (γ : GName) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isSema sema γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ v, ownSema γ v ∗
        (⌜uint.nat v > 0⌝ → ownSema γ (v - W32 1) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (@! runtime_Semacquire)) (Val #sema)) {{ Φ }} := by
  wp_start as #Hsem
  simp only [isSema_unseal, isSemaDef, ownSema_unseal, ownSemaDef]
  wp_for
  wp_bind (Primitive1 _ _)
  iinv Hsem with > ⟨%v, Hs, Hv⟩
  wp_apply_core wp_atomic_load _ _ sema _ v $$ Hs
  iintro Hs
  imodintro
  isplitl [Hs Hv]
  · inext; iexists v; iframe
  wp_auto
  wp_if_destruct
  · -- keep looping
    wp_for_post
    iframe
  · -- try to acquire
    wp_bind (CmpXchg _ _ _)
    iinv Hsem with > ⟨%v0, Hs, Hv⟩
    by_cases hv : v0 = v
    · subst hv
      imod HΦ with ⟨%v1, Hv2, HΦ⟩
      icombine Hv Hv2 gives % ⟨_, Heq⟩
      subst Heq
      imod ghostVar_update_halves (v0 - W32 1) γ v0 v0 $$ Hv Hv2 with ⟨Hv, Hv2⟩
      wp_apply_core wp_cmpxchg_suc sema v0 v0 (v0 - W32 1) _ _ rfl $$ Hs
      iintro Hs
      imod HΦ $$ [] Hv2 with HΦ
      · ipureintro
        have : (v0 : BitVec 32) ≠ 0 := Hif
        simp only [uint.nat]
        exact Nat.pos_of_ne_zero (fun h => this (BitVec.eq_of_toNat_eq h))
      imodintro
      imodintro
      isplitl [Hs Hv]
      · inext; iexists _; iframe
      wp_auto
      wp_for_post
      iexact HΦ
    · wp_apply_core wp_cmpxchg_fail sema v0 v _ _ _ _ hv $$ Hs
      iintro Hs
      imodintro
      isplitl [Hs Hv]
      · inext; iexists _; iframe
      wp_auto
      wp_for_post
      iframe

theorem wp_runtime_SemacquireWaitGroup (sema : Loc) (γ : GName) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isSema sema γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ v, ownSema γ v ∗
        (⌜uint.nat v > 0⌝ → ownSema γ (v - W32 1) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (App (Val (@! runtime_SemacquireWaitGroup)) (Val #sema)) (Val #false)) {{ Φ }} := by
  wp_start as #Hsem
  rw [show (go!"sync.runtime_Semacquire" : GoString) = runtime_Semacquire from rfl]
  wp_apply_core wp_runtime_Semacquire sema γ N $$ [] HΦ
  iframe #

theorem wp_runtime_SemacquireRWMutexR (sema : Loc) (γ : GName) (N : Namespace) (lifo : Bool) (skipframes : w64) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isSema sema γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ v, ownSema γ v ∗
        (⌜uint.nat v > 0⌝ → ownSema γ (v - W32 1) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (App (App (Val (@! runtime_SemacquireRWMutexR)) (Val #sema)) (Val #lifo)) (Val #skipframes)) {{ Φ }} := by
  wp_start as #Hsem
  rw [show (go!"sync.runtime_Semacquire" : GoString) = runtime_Semacquire from rfl]
  wp_apply_core wp_runtime_Semacquire sema γ N $$ [] HΦ
  iframe #

theorem wp_runtime_SemacquireRWMutex (sema : Loc) (γ : GName) (N : Namespace) (lifo : Bool) (skipframes : w64) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isSema sema γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ v, ownSema γ v ∗
        (⌜uint.nat v > 0⌝ → ownSema γ (v - W32 1) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (App (App (Val (@! runtime_SemacquireRWMutex)) (Val #sema)) (Val #lifo)) (Val #skipframes)) {{ Φ }} := by
  wp_start as #Hsem
  rw [show (go!"sync.runtime_Semacquire" : GoString) = runtime_Semacquire from rfl]
  wp_apply_core wp_runtime_Semacquire sema γ N $$ [] HΦ
  iframe #

theorem wp_runtime_Semrelease (sema : Loc) (γ : GName) (N : Namespace) (_u1 : Bool) (_u2 : w64) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isSema sema γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ v, ownSema γ v ∗
        (ownSema γ (v + W32 1) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (App (App (Val (@! runtime_Semrelease)) (Val #sema)) (Val #_u1)) (Val #_u2)) {{ Φ }} := by
  wp_start as #Hsem
  simp only [isSema_unseal, isSemaDef, ownSema_unseal, ownSemaDef]
  wp_bind (AtomicAdd _ _)
  iinv Hsem with > ⟨%v, Hs, Hv⟩
  imod HΦ with ⟨%v1, Hv2, HΦ⟩
  icombine Hv Hv2 gives % ⟨_, Heq⟩
  subst Heq
  simp only [typedPointsto_unseal, typedPointstoWrap, typedPointstoDef_heap]
  icases Hs with ⟨Hs, %Hnn⟩
  wp_apply_core Perennial.wp_atomic_add sema #v #(W32 1) #(v + W32 1)
    (by simp [go.intoVal_unfold, atomicAddEval]) $$ Hs
  iintro Hs
  imod ghostVar_update_halves (v + W32 1) γ v v $$ Hv Hv2 with ⟨Hv, Hv2⟩
  imod HΦ $$ Hv2 with HΦ
  imodintro
  imodintro
  isplitl [Hs Hv]
  · inext; iexists _
    simp only [typedPointsto_unseal, typedPointstoWrap, typedPointstoDef_heap]
    iframe; ipureintro; exact Hnn
  wp_auto
  iexact HΦ

end wps

end sync

end Perennial
end
