/-
Port of `new/proof/sync/atomic.v`: specs for `sync/atomic`, as logically
atomic updates (`|={⊤,∅}=> ▷ ∃ v, ... ∗ (... ={∅,⊤}=∗ Φ _)`).

The integer sections (Uint64, Int64, Uint32, Int32) are generated from one
template, as in Rocq (`int_template.py`).
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.sync.atomic
import Perennial.GeneratedProof.sync.atomic

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace sync.atomic

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.sync.atomic :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.sync.atomic :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.sync.atomic get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

/-! ### Uint64 -/

theorem wp_LoadUint64 (addr : loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w64, addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (@! LoadUint64)) (Val #addr)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%v, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_load _ _ addr dq v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_SwapUint64 (addr : loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
      WP (App (App (Val (@! SwapUint64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_swap _ _ addr oldv v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_StoreUint64 (addr : loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! StoreUint64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_bind (AtomicSwap _ _)
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_swap _ _ addr oldv v $$ Haddr
  iintro Haddr
  imod HΦ $$ Haddr with HΦ
  imodintro
  wp_pures
  iexact HΦ

theorem wp_AddUint64 (addr : loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗
        (addr ↦ (oldv + v) ={∅,⊤}=∗ Φ #(oldv + v))) -∗
      WP (App (App (Val (@! AddUint64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, Haddr, HΦ⟩
  simp only [typed_pointsto_unseal, typed_pointsto_wrap, typed_pointsto_def_heap,
    TypedPointsto.typed_pointsto_def]
  icases Haddr with > ⟨Haddr, %Hnn⟩
  wp_apply_core Perennial.wp_atomic_add addr #oldv #v #(oldv + v) (by simp [go.into_val_unfold, atomic_add_eval]) $$ Haddr
  iintro Haddr
  iapply HΦ
  iframe
  ipureintro; exact Hnn

theorem wp_CompareAndSwapUint64 (addr : loc) (old new : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w64) (dq : DFrac), addr ↦{dq} v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (addr ↦{dq} (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (App (Val (@! CompareAndSwapUint64)) (Val #addr)) (Val #old)) (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_bind (CmpXchg _ _ _)
  imod HΦ with ⟨%v, %dq, >Haddr, >%Hdq, HΦ⟩
  by_cases h : v = old
  · subst h
    simp only [↓reduceIte, decide_true] at Hdq ⊢
    subst Hdq
    wp_apply_core wp_cmpxchg_suc addr v v new _ _ rfl $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ
  · simp only [h, ↓reduceIte, decide_false]
    wp_apply_core wp_cmpxchg_fail addr v old new dq _ _ h $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ

def own_Uint64_def (u : loc) (dq : DFrac) (v : w64) : IProp GF :=
  typed_pointsto (GF := GF) u ({ _0' := zero_val _, _1' := zero_val _, v' := v : Uint64.t }) dq
@[irreducible] def own_Uint64 (u : loc) (dq : DFrac) (v : w64) : IProp GF := own_Uint64_def u dq v
theorem own_Uint64_unseal : @own_Uint64 = @own_Uint64_def := by funext; with_unfolding_all rfl

instance own_Uint64_timeless (u : loc) (dq : DFrac) (v : w64) :
    Timeless (own_Uint64 (GF := GF) u dq v) := by
  rw [own_Uint64_unseal]; unfold own_Uint64_def; infer_instance
instance own_Uint64_dfractional (u : loc) (v : w64) :
    DFractional (fun dq => own_Uint64 (GF := GF) u dq v) := by
  rw [own_Uint64_unseal]; unfold own_Uint64_def; infer_instance
instance own_Uint64_as_dfractional (u : loc) (v : w64) (dq : DFrac) :
    AsDFractional (own_Uint64 (GF := GF) u dq v) (fun dq => own_Uint64 u dq v) dq :=
  ⟨.rfl, own_Uint64_dfractional u v⟩
instance own_Uint64_fractional (u : loc) (v : w64) :
    Fractional (fun q => own_Uint64 (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => own_Uint64 (GF := GF) u dq v)
instance own_Uint64_combines_gives (u : loc) (v v' : w64) (dq dq' : DFrac) :
    CombineSepGives (own_Uint64 (GF := GF) u dq v) (own_Uint64 u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [own_Uint64_unseal]; unfold own_Uint64_def
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    cases Heq; rfl

theorem wp_Uint64__Load (u : loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w64, own_Uint64 u dq v ∗ (own_Uint64 u dq v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.type.PointerType Uint64 @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadUint64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Uint64_unseal, own_Uint64_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Uint64__Store (u : loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w64, own_Uint64 u (DFrac.own 1) old ∗
        (own_Uint64 u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (u @!! go.type.PointerType Uint64 @!! go!"Store")) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_StoreUint64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Uint64_unseal, own_Uint64_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Uint64__Add (u : loc) (delta : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w64, own_Uint64 u (DFrac.own 1) old ∗
        (own_Uint64 u (DFrac.own 1) (old + delta) ={∅,⊤}=∗ Φ #(old + delta))) -∗
      WP (App (Val (u @!! go.type.PointerType Uint64 @!! go!"Add")) (Val #delta)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_AddUint64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Uint64_unseal, own_Uint64_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Uint64__CompareAndSwap (u : loc) (old new : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w64) (dq : DFrac), own_Uint64 u dq v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (own_Uint64 u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (Val (u @!! go.type.PointerType Uint64 @!! go!"CompareAndSwap")) (Val #old))
        (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_CompareAndSwapUint64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [own_Uint64_unseal, own_Uint64_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v, dq
  iframe v
  isplitr
  · ipureintro; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

/-! ### Int64 -/

theorem wp_LoadInt64 (addr : loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w64, addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (@! LoadInt64)) (Val #addr)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%v, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_load _ _ addr dq v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_SwapInt64 (addr : loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
      WP (App (App (Val (@! SwapInt64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_swap _ _ addr oldv v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_StoreInt64 (addr : loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! StoreInt64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_bind (AtomicSwap _ _)
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_swap _ _ addr oldv v $$ Haddr
  iintro Haddr
  imod HΦ $$ Haddr with HΦ
  imodintro
  wp_pures
  iexact HΦ

theorem wp_AddInt64 (addr : loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗
        (addr ↦ (oldv + v) ={∅,⊤}=∗ Φ #(oldv + v))) -∗
      WP (App (App (Val (@! AddInt64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, Haddr, HΦ⟩
  simp only [typed_pointsto_unseal, typed_pointsto_wrap, typed_pointsto_def_heap,
    TypedPointsto.typed_pointsto_def]
  icases Haddr with > ⟨Haddr, %Hnn⟩
  wp_apply_core Perennial.wp_atomic_add addr #oldv #v #(oldv + v) (by simp [go.into_val_unfold, atomic_add_eval]) $$ Haddr
  iintro Haddr
  iapply HΦ
  iframe
  ipureintro; exact Hnn

theorem wp_CompareAndSwapInt64 (addr : loc) (old new : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w64) (dq : DFrac), addr ↦{dq} v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (addr ↦{dq} (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (App (Val (@! CompareAndSwapInt64)) (Val #addr)) (Val #old)) (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_bind (CmpXchg _ _ _)
  imod HΦ with ⟨%v, %dq, >Haddr, >%Hdq, HΦ⟩
  by_cases h : v = old
  · subst h
    simp only [↓reduceIte, decide_true] at Hdq ⊢
    subst Hdq
    wp_apply_core wp_cmpxchg_suc addr v v new _ _ rfl $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ
  · simp only [h, ↓reduceIte, decide_false]
    wp_apply_core wp_cmpxchg_fail addr v old new dq _ _ h $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ

def own_Int64_def (u : loc) (dq : DFrac) (v : w64) : IProp GF :=
  typed_pointsto (GF := GF) u ({ _0' := zero_val _, _1' := zero_val _, v' := v : Int64.t }) dq
@[irreducible] def own_Int64 (u : loc) (dq : DFrac) (v : w64) : IProp GF := own_Int64_def u dq v
theorem own_Int64_unseal : @own_Int64 = @own_Int64_def := by funext; with_unfolding_all rfl

instance own_Int64_timeless (u : loc) (dq : DFrac) (v : w64) :
    Timeless (own_Int64 (GF := GF) u dq v) := by
  rw [own_Int64_unseal]; unfold own_Int64_def; infer_instance
instance own_Int64_dfractional (u : loc) (v : w64) :
    DFractional (fun dq => own_Int64 (GF := GF) u dq v) := by
  rw [own_Int64_unseal]; unfold own_Int64_def; infer_instance
instance own_Int64_as_dfractional (u : loc) (v : w64) (dq : DFrac) :
    AsDFractional (own_Int64 (GF := GF) u dq v) (fun dq => own_Int64 u dq v) dq :=
  ⟨.rfl, own_Int64_dfractional u v⟩
instance own_Int64_fractional (u : loc) (v : w64) :
    Fractional (fun q => own_Int64 (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => own_Int64 (GF := GF) u dq v)
instance own_Int64_combines_gives (u : loc) (v v' : w64) (dq dq' : DFrac) :
    CombineSepGives (own_Int64 (GF := GF) u dq v) (own_Int64 u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [own_Int64_unseal]; unfold own_Int64_def
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    cases Heq; rfl

theorem wp_Int64__Load (u : loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w64, own_Int64 u dq v ∗ (own_Int64 u dq v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.type.PointerType Int64 @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadInt64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Int64_unseal, own_Int64_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Int64__Store (u : loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w64, own_Int64 u (DFrac.own 1) old ∗
        (own_Int64 u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (u @!! go.type.PointerType Int64 @!! go!"Store")) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_StoreInt64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Int64_unseal, own_Int64_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Int64__Add (u : loc) (delta : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w64, own_Int64 u (DFrac.own 1) old ∗
        (own_Int64 u (DFrac.own 1) (old + delta) ={∅,⊤}=∗ Φ #(old + delta))) -∗
      WP (App (Val (u @!! go.type.PointerType Int64 @!! go!"Add")) (Val #delta)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_AddInt64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Int64_unseal, own_Int64_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Int64__CompareAndSwap (u : loc) (old new : w64) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w64) (dq : DFrac), own_Int64 u dq v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (own_Int64 u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (Val (u @!! go.type.PointerType Int64 @!! go!"CompareAndSwap")) (Val #old))
        (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_CompareAndSwapInt64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [own_Int64_unseal, own_Int64_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v, dq
  iframe v
  isplitr
  · ipureintro; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

/-! ### Uint32 -/

theorem wp_LoadUint32 (addr : loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w32, addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (@! LoadUint32)) (Val #addr)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%v, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_load _ _ addr dq v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_SwapUint32 (addr : loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w32, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
      WP (App (App (Val (@! SwapUint32)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_swap _ _ addr oldv v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_StoreUint32 (addr : loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w32, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! StoreUint32)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_bind (AtomicSwap _ _)
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_swap _ _ addr oldv v $$ Haddr
  iintro Haddr
  imod HΦ $$ Haddr with HΦ
  imodintro
  wp_pures
  iexact HΦ

theorem wp_AddUint32 (addr : loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w32, addr ↦ oldv ∗
        (addr ↦ (oldv + v) ={∅,⊤}=∗ Φ #(oldv + v))) -∗
      WP (App (App (Val (@! AddUint32)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, Haddr, HΦ⟩
  simp only [typed_pointsto_unseal, typed_pointsto_wrap, typed_pointsto_def_heap,
    TypedPointsto.typed_pointsto_def]
  icases Haddr with > ⟨Haddr, %Hnn⟩
  wp_apply_core Perennial.wp_atomic_add addr #oldv #v #(oldv + v) (by simp [go.into_val_unfold, atomic_add_eval]) $$ Haddr
  iintro Haddr
  iapply HΦ
  iframe
  ipureintro; exact Hnn

theorem wp_CompareAndSwapUint32 (addr : loc) (old new : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w32) (dq : DFrac), addr ↦{dq} v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (addr ↦{dq} (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (App (Val (@! CompareAndSwapUint32)) (Val #addr)) (Val #old)) (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_bind (CmpXchg _ _ _)
  imod HΦ with ⟨%v, %dq, >Haddr, >%Hdq, HΦ⟩
  by_cases h : v = old
  · subst h
    simp only [↓reduceIte, decide_true] at Hdq ⊢
    subst Hdq
    wp_apply_core wp_cmpxchg_suc addr v v new _ _ rfl $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ
  · simp only [h, ↓reduceIte, decide_false]
    wp_apply_core wp_cmpxchg_fail addr v old new dq _ _ h $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ

def own_Uint32_def (u : loc) (dq : DFrac) (v : w32) : IProp GF :=
  typed_pointsto (GF := GF) u ({ _0' := zero_val _, v' := v : Uint32.t }) dq
@[irreducible] def own_Uint32 (u : loc) (dq : DFrac) (v : w32) : IProp GF := own_Uint32_def u dq v
theorem own_Uint32_unseal : @own_Uint32 = @own_Uint32_def := by funext; with_unfolding_all rfl

instance own_Uint32_timeless (u : loc) (dq : DFrac) (v : w32) :
    Timeless (own_Uint32 (GF := GF) u dq v) := by
  rw [own_Uint32_unseal]; unfold own_Uint32_def; infer_instance
instance own_Uint32_dfractional (u : loc) (v : w32) :
    DFractional (fun dq => own_Uint32 (GF := GF) u dq v) := by
  rw [own_Uint32_unseal]; unfold own_Uint32_def; infer_instance
instance own_Uint32_as_dfractional (u : loc) (v : w32) (dq : DFrac) :
    AsDFractional (own_Uint32 (GF := GF) u dq v) (fun dq => own_Uint32 u dq v) dq :=
  ⟨.rfl, own_Uint32_dfractional u v⟩
instance own_Uint32_fractional (u : loc) (v : w32) :
    Fractional (fun q => own_Uint32 (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => own_Uint32 (GF := GF) u dq v)
instance own_Uint32_combines_gives (u : loc) (v v' : w32) (dq dq' : DFrac) :
    CombineSepGives (own_Uint32 (GF := GF) u dq v) (own_Uint32 u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [own_Uint32_unseal]; unfold own_Uint32_def
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    cases Heq; rfl

theorem wp_Uint32__Load (u : loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w32, own_Uint32 u dq v ∗ (own_Uint32 u dq v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.type.PointerType Uint32 @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Uint32_unseal, own_Uint32_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Uint32__Store (u : loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w32, own_Uint32 u (DFrac.own 1) old ∗
        (own_Uint32 u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (u @!! go.type.PointerType Uint32 @!! go!"Store")) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_StoreUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Uint32_unseal, own_Uint32_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Uint32__Add (u : loc) (delta : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w32, own_Uint32 u (DFrac.own 1) old ∗
        (own_Uint32 u (DFrac.own 1) (old + delta) ={∅,⊤}=∗ Φ #(old + delta))) -∗
      WP (App (Val (u @!! go.type.PointerType Uint32 @!! go!"Add")) (Val #delta)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_AddUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Uint32_unseal, own_Uint32_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Uint32__CompareAndSwap (u : loc) (old new : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w32) (dq : DFrac), own_Uint32 u dq v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (own_Uint32 u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (Val (u @!! go.type.PointerType Uint32 @!! go!"CompareAndSwap")) (Val #old))
        (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_CompareAndSwapUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [own_Uint32_unseal, own_Uint32_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v, dq
  iframe v
  isplitr
  · ipureintro; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

/-! ### Int32 -/

theorem wp_LoadInt32 (addr : loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w32, addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (@! LoadInt32)) (Val #addr)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%v, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_load _ _ addr dq v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_SwapInt32 (addr : loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w32, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
      WP (App (App (Val (@! SwapInt32)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_swap _ _ addr oldv v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_StoreInt32 (addr : loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w32, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! StoreInt32)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_bind (AtomicSwap _ _)
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_swap _ _ addr oldv v $$ Haddr
  iintro Haddr
  imod HΦ $$ Haddr with HΦ
  imodintro
  wp_pures
  iexact HΦ

theorem wp_AddInt32 (addr : loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w32, addr ↦ oldv ∗
        (addr ↦ (oldv + v) ={∅,⊤}=∗ Φ #(oldv + v))) -∗
      WP (App (App (Val (@! AddInt32)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, Haddr, HΦ⟩
  simp only [typed_pointsto_unseal, typed_pointsto_wrap, typed_pointsto_def_heap,
    TypedPointsto.typed_pointsto_def]
  icases Haddr with > ⟨Haddr, %Hnn⟩
  wp_apply_core Perennial.wp_atomic_add addr #oldv #v #(oldv + v) (by simp [go.into_val_unfold, atomic_add_eval]) $$ Haddr
  iintro Haddr
  iapply HΦ
  iframe
  ipureintro; exact Hnn

theorem wp_CompareAndSwapInt32 (addr : loc) (old new : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w32) (dq : DFrac), addr ↦{dq} v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (addr ↦{dq} (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (App (Val (@! CompareAndSwapInt32)) (Val #addr)) (Val #old)) (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_bind (CmpXchg _ _ _)
  imod HΦ with ⟨%v, %dq, >Haddr, >%Hdq, HΦ⟩
  by_cases h : v = old
  · subst h
    simp only [↓reduceIte, decide_true] at Hdq ⊢
    subst Hdq
    wp_apply_core wp_cmpxchg_suc addr v v new _ _ rfl $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ
  · simp only [h, ↓reduceIte, decide_false]
    wp_apply_core wp_cmpxchg_fail addr v old new dq _ _ h $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ

def own_Int32_def (u : loc) (dq : DFrac) (v : w32) : IProp GF :=
  typed_pointsto (GF := GF) u ({ _0' := zero_val _, v' := v : Int32.t }) dq
@[irreducible] def own_Int32 (u : loc) (dq : DFrac) (v : w32) : IProp GF := own_Int32_def u dq v
theorem own_Int32_unseal : @own_Int32 = @own_Int32_def := by funext; with_unfolding_all rfl

instance own_Int32_timeless (u : loc) (dq : DFrac) (v : w32) :
    Timeless (own_Int32 (GF := GF) u dq v) := by
  rw [own_Int32_unseal]; unfold own_Int32_def; infer_instance
instance own_Int32_dfractional (u : loc) (v : w32) :
    DFractional (fun dq => own_Int32 (GF := GF) u dq v) := by
  rw [own_Int32_unseal]; unfold own_Int32_def; infer_instance
instance own_Int32_as_dfractional (u : loc) (v : w32) (dq : DFrac) :
    AsDFractional (own_Int32 (GF := GF) u dq v) (fun dq => own_Int32 u dq v) dq :=
  ⟨.rfl, own_Int32_dfractional u v⟩
instance own_Int32_fractional (u : loc) (v : w32) :
    Fractional (fun q => own_Int32 (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => own_Int32 (GF := GF) u dq v)
instance own_Int32_combines_gives (u : loc) (v v' : w32) (dq dq' : DFrac) :
    CombineSepGives (own_Int32 (GF := GF) u dq v) (own_Int32 u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [own_Int32_unseal]; unfold own_Int32_def
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    cases Heq; rfl

theorem wp_Int32__Load (u : loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w32, own_Int32 u dq v ∗ (own_Int32 u dq v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.type.PointerType Int32 @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadInt32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Int32_unseal, own_Int32_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Int32__Store (u : loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w32, own_Int32 u (DFrac.own 1) old ∗
        (own_Int32 u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (u @!! go.type.PointerType Int32 @!! go!"Store")) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_StoreInt32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Int32_unseal, own_Int32_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Int32__Add (u : loc) (delta : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w32, own_Int32 u (DFrac.own 1) old ∗
        (own_Int32 u (DFrac.own 1) (old + delta) ={∅,⊤}=∗ Φ #(old + delta))) -∗
      WP (App (Val (u @!! go.type.PointerType Int32 @!! go!"Add")) (Val #delta)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_AddInt32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Int32_unseal, own_Int32_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Int32__CompareAndSwap (u : loc) (old new : w32) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w32) (dq : DFrac), own_Int32 u dq v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (own_Int32 u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (Val (u @!! go.type.PointerType Int32 @!! go!"CompareAndSwap")) (Val #old))
        (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_CompareAndSwapInt32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [own_Int32_unseal, own_Int32_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v, dq
  iframe v
  isplitr
  · ipureintro; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

/-! ### Pointer -/

theorem wp_LoadPointer (addr : loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : loc, addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (@! LoadPointer)) (Val #addr)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%v, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_load _ _ addr dq v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_SwapPointer (addr : loc) (v : loc) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : loc, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
      WP (App (App (Val (@! SwapPointer)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_swap _ _ addr oldv v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_StorePointer (addr : loc) (v : loc) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : loc, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! StorePointer)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_bind (AtomicSwap _ _)
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_swap _ _ addr oldv v $$ Haddr
  iintro Haddr
  imod HΦ $$ Haddr with HΦ
  imodintro
  wp_pures
  iexact HΦ

theorem wp_CompareAndSwapPointer (addr : loc) (old new : loc) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : loc) (dq : DFrac), addr ↦{dq} v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (addr ↦{dq} (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (App (Val (@! CompareAndSwapPointer)) (Val #addr)) (Val #old)) (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_bind (CmpXchg _ _ _)
  imod HΦ with ⟨%v, %dq, >Haddr, >%Hdq, HΦ⟩
  by_cases h : v = old
  · subst h
    simp only [↓reduceIte, decide_true] at Hdq ⊢
    subst Hdq
    wp_apply_core wp_cmpxchg_suc addr v v new _ _ rfl $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ
  · simp only [h, ↓reduceIte, decide_false]
    wp_apply_core wp_cmpxchg_fail addr v old new dq _ _ h $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ


section pointer
variable {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.type) [IntoValTyped (GF := GF) T' T]

def own_Pointer_def (u : loc) (dq : DFrac) (v : loc) : IProp GF :=
  typed_pointsto (GF := GF) u ({ _0' := zero_val _, _1' := zero_val _, v' := v } : Pointer.t T') dq
@[irreducible] def own_Pointer (u : loc) (dq : DFrac) (v : loc) : IProp GF :=
  own_Pointer_def (T' := T') u dq v
theorem own_Pointer_unseal : @own_Pointer = @own_Pointer_def := by funext; with_unfolding_all rfl

instance own_Pointer_timeless (u : loc) (dq : DFrac) (v : loc) :
    Timeless (own_Pointer (GF := GF) (T' := T') u dq v) := by
  rw [own_Pointer_unseal]; unfold own_Pointer_def; infer_instance

theorem wp_Pointer__Load (u : loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : loc, own_Pointer (T' := T') u dq v ∗ (own_Pointer (T' := T') u dq v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.type.PointerType (Pointer T) @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadPointer $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Pointer_unseal, own_Pointer_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Pointer__Store (u : loc) (v : loc) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : loc, own_Pointer (T' := T') u (DFrac.own 1) old ∗
        (own_Pointer (T' := T') u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (u @!! go.type.PointerType (Pointer T) @!! go!"Store")) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_StorePointer $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Pointer_unseal, own_Pointer_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Pointer__CompareAndSwap (u : loc) (old new : loc) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : loc) (dq : DFrac), own_Pointer (T' := T') u dq v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (own_Pointer (T' := T') u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (Val (u @!! go.type.PointerType (Pointer T) @!! go!"CompareAndSwap")) (Val #old))
        (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_CompareAndSwapPointer $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [own_Pointer_unseal, own_Pointer_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v, dq
  iframe v
  isplitr
  · ipureintro; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Pointer__Swap (u : loc) (v' : loc) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ∃ v : loc, own_Pointer (T' := T') u (DFrac.own 1) v ∗
        (own_Pointer (T' := T') u (DFrac.own 1) v' ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.type.PointerType (Pointer T) @!! go!"Swap")) (Val #v')) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_SwapPointer $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Pointer_unseal, own_Pointer_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

end pointer

/-! ### Bool -/

/-- Rocq `b32` (renamed: `sync.atomic.b32` is the Go function's name). -/
def b32w (b : Bool) : w32 := if b then W32 1 else W32 0

theorem b32w_inj {b1 b2 : Bool} (h : b32w b1 = b32w b2) : b1 = b2 := by
  cases b1 <;> cases b2 <;> first | rfl | (exfalso; revert h; decide)

def own_Bool_def (u : loc) (dq : DFrac) (v : Bool) : IProp GF :=
  typed_pointsto (GF := GF) u ({ _0' := zero_val _, v' := b32w v } : Bool'.t) dq
@[irreducible] def own_Bool (u : loc) (dq : DFrac) (v : Bool) : IProp GF := own_Bool_def u dq v
theorem own_Bool_unseal : @own_Bool = @own_Bool_def := by funext; with_unfolding_all rfl

instance own_Bool_timeless (u : loc) (dq : DFrac) (v : Bool) :
    Timeless (own_Bool (GF := GF) u dq v) := by
  rw [own_Bool_unseal]; unfold own_Bool_def; infer_instance
instance own_Bool_dfractional (u : loc) (v : Bool) :
    DFractional (fun dq => own_Bool (GF := GF) u dq v) := by
  rw [own_Bool_unseal]; unfold own_Bool_def; infer_instance
instance own_Bool_fractional (u : loc) (v : Bool) :
    Fractional (fun q => own_Bool (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => own_Bool (GF := GF) u dq v)
instance own_Bool_as_fractional (u : loc) (q : Qp) (v : Bool) :
    AsFractional (own_Bool (GF := GF) u (DFrac.own q) v) ioΦ
      (fun q => own_Bool u (DFrac.own q) v) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := own_Bool_fractional u v
instance own_Bool_combines_gives (u : loc) (v v' : Bool) (dq dq' : DFrac) :
    CombineSepGives (own_Bool (GF := GF) u dq v) (own_Bool u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [own_Bool_unseal]; unfold own_Bool_def
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    exact b32w_inj (congrArg Bool'.t.v' Heq)

theorem wp_Bool__Load (u : loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : Bool, own_Bool u dq v ∗ (own_Bool u dq v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.type.PointerType Bool' @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Bool_unseal, own_Bool_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists (b32w v)
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  cases v <;> simp [b32w] <;> iexact HΦ

theorem wp_b32 (b : Bool) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      Φ #(b32w b) -∗ WP (App (Val (@! b32)) (Val #b)) {{ Φ }} := by
  wp_start as _
  cases b <;> simp only [b32w, Bool.false_eq_true, ↓reduceIte] <;> wp_auto <;> iexact HΦ

theorem wp_Bool__Store (u : loc) (v : Bool) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : Bool, own_Bool u (DFrac.own 1) old ∗
        (own_Bool u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (u @!! go.type.PointerType Bool' @!! go!"Store")) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply wp_b32
  wp_apply_core wp_StoreUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [own_Bool_unseal, own_Bool_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists (b32w old)
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem wp_Bool__CompareAndSwap (u : loc) (old new : Bool) :
    ⊢ ∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : Bool) (dq : DFrac), own_Bool u dq v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (own_Bool u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (Val (u @!! go.type.PointerType Bool' @!! go!"CompareAndSwap")) (Val #old))
        (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply wp_b32
  wp_apply wp_b32
  wp_apply_core wp_CompareAndSwapUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [own_Bool_unseal, own_Bool_def]
  ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  have hiff : (b32w v = b32w old) ↔ (v = old) := ⟨b32w_inj, fun h => h ▸ rfl⟩
  iexists (b32w v), dq
  iframe v
  isplitr
  · ipureintro; simp only [hiff]; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    iframe
    by_cases h : v = old <;> simp [h, hiff]
    · iexact Hv
    · iexact Hv
  imodintro
  wp_auto
  simp only [decide_eq_decide.mpr hiff]
  iexact HΦ
end wps

end sync.atomic

end Perennial
end
