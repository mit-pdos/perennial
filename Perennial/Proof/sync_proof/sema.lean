/-
Port of `new/proof/sync_proof/sema.v`: the runtime semaphore used by `sync`.
-/
import Perennial.Proof.sync_proof.base

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace sync

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The semaphore invariant. -/
abbrev sema_inv (x : loc) (γ : GName) : IProp GF :=
  iprop(∃ v : w32, x ↦ v ∗ ghost_var γ (1 : Qp).half v)

def is_sema_def (x : loc) (γ : GName) (N : Namespace) : IProp GF := inv N (sema_inv x γ)
@[irreducible] def is_sema (x : loc) (γ : GName) (N : Namespace) : IProp GF := is_sema_def x γ N
theorem is_sema_unseal : @is_sema = @is_sema_def := by funext; with_unfolding_all rfl

instance is_sema_persistent (x : loc) (γ : GName) (N : Namespace) :
    Persistent (is_sema (GF := GF) x γ N) := by
  rw [is_sema_unseal]; unfold is_sema_def; infer_instance

def own_sema_def (γ : GName) (v : w32) : IProp GF := ghost_var γ (1 : Qp).half v
@[irreducible] def own_sema (γ : GName) (v : w32) : IProp GF := own_sema_def γ v
theorem own_sema_unseal : @own_sema = @own_sema_def := by funext; with_unfolding_all rfl

instance own_sema_timeless (γ : GName) (v : w32) : Timeless (own_sema (GF := GF) γ v) := by
  rw [own_sema_unseal]; unfold own_sema_def; infer_instance

theorem init_sema {E : CoPset} (N : Namespace) (sema : loc) (v : w32) :
    ⊢ typed_pointsto (GF := GF) sema v (DFrac.own 1) ={E}=∗
      ∃ γ, is_sema sema γ N ∗ own_sema γ v := by
  iintro Hs
  imod ghost_var_alloc v with ⟨%γ, Hv⟩
  icases ghost_var_split γ v (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
  · rw [Qp.half_add_half]; iexact Hv
  imod inv_alloc N E (sema_inv sema γ) $$ [Hs Hv1] with #Hinv
  · inext; iexists v; iframe
  imodintro
  iexists γ
  simp only [is_sema_unseal, is_sema_def, own_sema_unseal, own_sema_def]
  iframe # ∗

theorem wp_runtime_Semacquire (sema : loc) (γ : GName) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_sema sema γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ v, own_sema γ v ∗
        (⌜uint.nat v > 0⌝ → own_sema γ (v - W32 1) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (@! runtime_Semacquire)) (Val #sema)) {{ Φ }} := by
  wp_start as #Hsem
  simp only [is_sema_unseal, is_sema_def, own_sema_unseal, own_sema_def]
  wp_for
  wp_bind (Primitive1 _ _)
  iinv Hsem with ⟨%v, >Hs, Hv⟩
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
    iinv Hsem with ⟨%v0, >Hs, >Hv⟩
    by_cases hv : v0 = v
    · subst hv
      imod HΦ with ⟨%v1, Hv2, HΦ⟩
      icombine Hv Hv2 gives % ⟨_, Heq⟩
      subst Heq
      imod ghost_var_update_halves (v0 - W32 1) γ v0 v0 $$ Hv Hv2 with ⟨Hv, Hv2⟩
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

theorem wp_runtime_SemacquireWaitGroup (sema : loc) (γ : GName) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_sema sema γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ v, own_sema γ v ∗
        (⌜uint.nat v > 0⌝ → own_sema γ (v - W32 1) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (App (Val (@! runtime_SemacquireWaitGroup)) (Val #sema)) (Val #false)) {{ Φ }} := by
  wp_start as #Hsem
  rw [show (go!"sync.runtime_Semacquire" : go_string) = runtime_Semacquire from rfl]
  wp_apply_core wp_runtime_Semacquire sema γ N $$ [] HΦ
  iframe #

theorem wp_runtime_SemacquireRWMutexR (sema : loc) (γ : GName) (N : Namespace) (lifo : Bool) (skipframes : w64) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_sema sema γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ v, own_sema γ v ∗
        (⌜uint.nat v > 0⌝ → own_sema γ (v - W32 1) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (App (App (Val (@! runtime_SemacquireRWMutexR)) (Val #sema)) (Val #lifo)) (Val #skipframes)) {{ Φ }} := by
  wp_start as #Hsem
  rw [show (go!"sync.runtime_Semacquire" : go_string) = runtime_Semacquire from rfl]
  wp_apply_core wp_runtime_Semacquire sema γ N $$ [] HΦ
  iframe #

theorem wp_runtime_SemacquireRWMutex (sema : loc) (γ : GName) (N : Namespace) (lifo : Bool) (skipframes : w64) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_sema sema γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ v, own_sema γ v ∗
        (⌜uint.nat v > 0⌝ → own_sema γ (v - W32 1) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (App (App (Val (@! runtime_SemacquireRWMutex)) (Val #sema)) (Val #lifo)) (Val #skipframes)) {{ Φ }} := by
  wp_start as #Hsem
  rw [show (go!"sync.runtime_Semacquire" : go_string) = runtime_Semacquire from rfl]
  wp_apply_core wp_runtime_Semacquire sema γ N $$ [] HΦ
  iframe #

theorem wp_runtime_Semrelease (sema : loc) (γ : GName) (N : Namespace) (_u1 : Bool) (_u2 : w64) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_sema sema γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ v, own_sema γ v ∗
        (own_sema γ (v + W32 1) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (App (App (Val (@! runtime_Semrelease)) (Val #sema)) (Val #_u1)) (Val #_u2)) {{ Φ }} := by
  wp_start as #Hsem
  simp only [is_sema_unseal, is_sema_def, own_sema_unseal, own_sema_def]
  wp_bind (AtomicAdd _ _)
  iinv Hsem with ⟨%v, >Hs, >Hv⟩
  imod HΦ with ⟨%v1, Hv2, HΦ⟩
  icombine Hv Hv2 gives % ⟨_, Heq⟩
  subst Heq
  simp only [typed_pointsto_unseal, typed_pointsto_wrap, typed_pointsto_def_heap]
  icases Hs with ⟨Hs, %Hnn⟩
  wp_apply_core Perennial.wp_atomic_add sema #v #(W32 1) #(v + W32 1)
    (by simp [go.into_val_unfold, atomic_add_eval]) $$ Hs
  iintro Hs
  imod ghost_var_update_halves (v + W32 1) γ v v $$ Hv Hv2 with ⟨Hv, Hv2⟩
  imod HΦ $$ Hv2 with HΦ
  imodintro
  imodintro
  isplitl [Hs Hv]
  · inext; iexists _
    simp only [typed_pointsto_unseal, typed_pointsto_wrap, typed_pointsto_def_heap]
    iframe; ipureintro; exact Hnn
  wp_auto
  iexact HΦ

end wps

end sync

end Perennial
end
