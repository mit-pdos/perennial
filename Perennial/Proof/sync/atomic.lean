/-
Specs for `sync/atomic` (including the trusted model of `Value`, see its section), as logically
atomic updates (`|={⊤,∅}=> ▷ ∃ v, ... ∗ (... ={∅,⊤}=∗ Φ _)`).

The integer sections (Uint64, Int64, Uint32, Int32) follow one template and
differ only in the integer type.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.sync.atomic
public import Perennial.GeneratedProof.sync.atomic

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace sync.atomic

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.sync.atomic :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.sync.atomic :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.sync.atomic get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.sync.atomic }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

/-! ### Uint64 -/

theorem wp_LoadUint64 (addr : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w64, addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (@! LoadUint64)) (Val #addr)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%v, >Haddr, HΦ⟩
  wp_apply_core wp_word_load addr dq v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_SwapUint64 (addr : Loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
      WP (App (App (Val (@! SwapUint64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_word_swap addr oldv v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_StoreUint64 (addr : Loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! StoreUint64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_bind (AtomicWord _ _ _ _)
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_word_swap addr oldv v $$ Haddr
  iintro Haddr
  imod HΦ $$ Haddr with HΦ
  imodintro
  wp_pures
  iexact HΦ

theorem wp_AddUint64 (addr : Loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗
        (addr ↦ (oldv + v) ={∅,⊤}=∗ Φ #(oldv + v))) -∗
      WP (App (App (Val (@! AddUint64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_word_add addr oldv v (oldv + v) (toZ_add_w64 oldv v) $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

/-- (Time receipts) `wp_AddUint64` for the call
`atomic.AddUint64(addr, v)` before the function is resolved, i.e. in the form
in which goose emits it. Resolving `AddUint64` is a Go instruction, which yields
a time receipt `⧗ 1`; the atomic update receives it (so it can, e.g., be stored
in an invariant opened by the update). -/
theorem wp_AddUint64_receipt (addr : Loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (⧗ 1 -∗ |={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗
        (addr ↦ (oldv + v) ={∅,⊤}=∗ Φ #(oldv + v))) -∗
      WP (App (App (App (Val (GoInstruction (FuncResolve AddUint64 []))) (Val #())) (Val #addr))
        (Val #v)) {{ Φ }} := by
  iintro %Φ #Hpkg HΦ
  wp_bind (App (Val (GoInstruction _)) (Val _))
  iapply wp_go_step_receipt'
  inext
  iintro Hr _
  iapply wp_value'
  iapply wp_AddUint64 addr v $$ %Φ Hpkg
  iapply HΦ $$ Hr

theorem wp_CompareAndSwapUint64 (addr : Loc) (old new : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w64) (dq : DFrac), addr ↦{dq} v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (addr ↦{dq} (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (App (Val (@! CompareAndSwapUint64)) (Val #addr)) (Val #old)) (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_bind (AtomicWord _ _ _ _)
  imod HΦ with ⟨%v, %dq, >Haddr, >%Hdq, HΦ⟩
  by_cases h : v = old
  · subst h
    simp only [↓reduceIte, decide_true] at Hdq ⊢
    subst Hdq
    wp_apply_core wp_word_cmpxchg_suc addr v v new rfl $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ
  · simp only [h, ↓reduceIte, decide_false]
    wp_apply_core wp_word_cmpxchg_fail addr dq v old new h $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ

def ownUint64Def (u : Loc) (dq : DFrac) (v : w64) : IProp GF :=
  typedPointsto (GF := GF) u ({ _0' := zero_val _, _1' := zero_val _, v' := v : Uint64 }) dq
@[irreducible] def ownUint64 (u : Loc) (dq : DFrac) (v : w64) : IProp GF := ownUint64Def u dq v
theorem ownUint64_unseal : @ownUint64 = @ownUint64Def := by funext; with_unfolding_all rfl

instance ownUint64_timeless (u : Loc) (dq : DFrac) (v : w64) :
    Timeless (ownUint64 (GF := GF) u dq v) := by
  rw [ownUint64_unseal]; unfold ownUint64Def; infer_instance
instance ownUint64_dfractional (u : Loc) (v : w64) :
    DFractional (fun dq => ownUint64 (GF := GF) u dq v) := by
  rw [ownUint64_unseal]; unfold ownUint64Def; infer_instance
instance ownUint64_as_dfractional (u : Loc) (v : w64) (dq : DFrac) :
    AsDFractional (ownUint64 (GF := GF) u dq v) (fun dq => ownUint64 u dq v) dq :=
  ⟨.rfl, ownUint64_dfractional u v⟩
instance ownUint64_fractional (u : Loc) (v : w64) :
    Fractional (fun q => ownUint64 (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => ownUint64 (GF := GF) u dq v)
instance ownUint64_combines_gives (u : Loc) (v v' : w64) (dq dq' : DFrac) :
    CombineSepGives (ownUint64 (GF := GF) u dq v) (ownUint64 u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [ownUint64_unseal]; unfold ownUint64Def
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    cases Heq; rfl

theorem Uint64.wp_Load (u : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w64, ownUint64 u dq v ∗ (ownUint64 u dq v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.GoType.PointerType Uint64.ty @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadUint64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [ownUint64_unseal, ownUint64Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Uint64.wp_Store (u : Loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w64, ownUint64 u (DFrac.own 1) old ∗
        (ownUint64 u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (u @!! go.GoType.PointerType Uint64.ty @!! go!"Store")) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_StoreUint64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownUint64_unseal, ownUint64Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Uint64.wp_Add (u : Loc) (delta : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w64, ownUint64 u (DFrac.own 1) old ∗
        (ownUint64 u (DFrac.own 1) (old + delta) ={∅,⊤}=∗ Φ #(old + delta))) -∗
      WP (App (Val (u @!! go.GoType.PointerType Uint64.ty @!! go!"Add")) (Val #delta)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_AddUint64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownUint64_unseal, ownUint64Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Uint64.wp_CompareAndSwap (u : Loc) (old new : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w64) (dq : DFrac), ownUint64 u dq v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (ownUint64 u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (Val (u @!! go.GoType.PointerType Uint64.ty @!! go!"CompareAndSwap")) (Val #old))
        (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_CompareAndSwapUint64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [ownUint64_unseal, ownUint64Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v, dq
  iframe v
  isplitr
  · ipureintro; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

/-! ### Int64 -/

theorem wp_LoadInt64 (addr : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w64, addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (@! LoadInt64)) (Val #addr)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%v, >Haddr, HΦ⟩
  wp_apply_core wp_word_load addr dq v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_SwapInt64 (addr : Loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
      WP (App (App (Val (@! SwapInt64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_word_swap addr oldv v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_StoreInt64 (addr : Loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! StoreInt64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_bind (AtomicWord _ _ _ _)
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_word_swap addr oldv v $$ Haddr
  iintro Haddr
  imod HΦ $$ Haddr with HΦ
  imodintro
  wp_pures
  iexact HΦ

theorem wp_AddInt64 (addr : Loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗
        (addr ↦ (oldv + v) ={∅,⊤}=∗ Φ #(oldv + v))) -∗
      WP (App (App (Val (@! AddInt64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_word_add addr oldv v (oldv + v) (toZ_add_w64 oldv v) $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_CompareAndSwapInt64 (addr : Loc) (old new : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w64) (dq : DFrac), addr ↦{dq} v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (addr ↦{dq} (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (App (Val (@! CompareAndSwapInt64)) (Val #addr)) (Val #old)) (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_bind (AtomicWord _ _ _ _)
  imod HΦ with ⟨%v, %dq, >Haddr, >%Hdq, HΦ⟩
  by_cases h : v = old
  · subst h
    simp only [↓reduceIte, decide_true] at Hdq ⊢
    subst Hdq
    wp_apply_core wp_word_cmpxchg_suc addr v v new rfl $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ
  · simp only [h, ↓reduceIte, decide_false]
    wp_apply_core wp_word_cmpxchg_fail addr dq v old new h $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ

def ownInt64Def (u : Loc) (dq : DFrac) (v : w64) : IProp GF :=
  typedPointsto (GF := GF) u ({ _0' := zero_val _, _1' := zero_val _, v' := v : Int64 }) dq
@[irreducible] def ownInt64 (u : Loc) (dq : DFrac) (v : w64) : IProp GF := ownInt64Def u dq v
theorem ownInt64_unseal : @ownInt64 = @ownInt64Def := by funext; with_unfolding_all rfl

instance ownInt64_timeless (u : Loc) (dq : DFrac) (v : w64) :
    Timeless (ownInt64 (GF := GF) u dq v) := by
  rw [ownInt64_unseal]; unfold ownInt64Def; infer_instance
instance ownInt64_dfractional (u : Loc) (v : w64) :
    DFractional (fun dq => ownInt64 (GF := GF) u dq v) := by
  rw [ownInt64_unseal]; unfold ownInt64Def; infer_instance
instance ownInt64_as_dfractional (u : Loc) (v : w64) (dq : DFrac) :
    AsDFractional (ownInt64 (GF := GF) u dq v) (fun dq => ownInt64 u dq v) dq :=
  ⟨.rfl, ownInt64_dfractional u v⟩
instance ownInt64_fractional (u : Loc) (v : w64) :
    Fractional (fun q => ownInt64 (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => ownInt64 (GF := GF) u dq v)
instance ownInt64_combines_gives (u : Loc) (v v' : w64) (dq dq' : DFrac) :
    CombineSepGives (ownInt64 (GF := GF) u dq v) (ownInt64 u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [ownInt64_unseal]; unfold ownInt64Def
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    cases Heq; rfl

theorem Int64.wp_Load (u : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w64, ownInt64 u dq v ∗ (ownInt64 u dq v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.GoType.PointerType Int64.ty @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadInt64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [ownInt64_unseal, ownInt64Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Int64.wp_Store (u : Loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w64, ownInt64 u (DFrac.own 1) old ∗
        (ownInt64 u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (u @!! go.GoType.PointerType Int64.ty @!! go!"Store")) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_StoreInt64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownInt64_unseal, ownInt64Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Int64.wp_Add (u : Loc) (delta : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w64, ownInt64 u (DFrac.own 1) old ∗
        (ownInt64 u (DFrac.own 1) (old + delta) ={∅,⊤}=∗ Φ #(old + delta))) -∗
      WP (App (Val (u @!! go.GoType.PointerType Int64.ty @!! go!"Add")) (Val #delta)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_AddInt64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownInt64_unseal, ownInt64Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Int64.wp_CompareAndSwap (u : Loc) (old new : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w64) (dq : DFrac), ownInt64 u dq v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (ownInt64 u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (Val (u @!! go.GoType.PointerType Int64.ty @!! go!"CompareAndSwap")) (Val #old))
        (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_CompareAndSwapInt64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [ownInt64_unseal, ownInt64Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v, dq
  iframe v
  isplitr
  · ipureintro; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

/-! ### Uint32 -/

theorem wp_LoadUint32 (addr : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w32, addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (@! LoadUint32)) (Val #addr)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%v, >Haddr, HΦ⟩
  wp_apply_core wp_word_load addr dq v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_SwapUint32 (addr : Loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w32, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
      WP (App (App (Val (@! SwapUint32)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_word_swap addr oldv v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_StoreUint32 (addr : Loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w32, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! StoreUint32)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_bind (AtomicWord _ _ _ _)
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_word_swap addr oldv v $$ Haddr
  iintro Haddr
  imod HΦ $$ Haddr with HΦ
  imodintro
  wp_pures
  iexact HΦ

theorem wp_AddUint32 (addr : Loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w32, addr ↦ oldv ∗
        (addr ↦ (oldv + v) ={∅,⊤}=∗ Φ #(oldv + v))) -∗
      WP (App (App (Val (@! AddUint32)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_word_add addr oldv v (oldv + v) (toZ_add_w32 oldv v) $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_CompareAndSwapUint32 (addr : Loc) (old new : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w32) (dq : DFrac), addr ↦{dq} v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (addr ↦{dq} (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (App (Val (@! CompareAndSwapUint32)) (Val #addr)) (Val #old)) (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_bind (AtomicWord _ _ _ _)
  imod HΦ with ⟨%v, %dq, >Haddr, >%Hdq, HΦ⟩
  by_cases h : v = old
  · subst h
    simp only [↓reduceIte, decide_true] at Hdq ⊢
    subst Hdq
    wp_apply_core wp_word_cmpxchg_suc addr v v new rfl $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ
  · simp only [h, ↓reduceIte, decide_false]
    wp_apply_core wp_word_cmpxchg_fail addr dq v old new h $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ

def ownUint32Def (u : Loc) (dq : DFrac) (v : w32) : IProp GF :=
  typedPointsto (GF := GF) u ({ _0' := zero_val _, v' := v : Uint32 }) dq
@[irreducible] def ownUint32 (u : Loc) (dq : DFrac) (v : w32) : IProp GF := ownUint32Def u dq v
theorem ownUint32_unseal : @ownUint32 = @ownUint32Def := by funext; with_unfolding_all rfl

instance ownUint32_timeless (u : Loc) (dq : DFrac) (v : w32) :
    Timeless (ownUint32 (GF := GF) u dq v) := by
  rw [ownUint32_unseal]; unfold ownUint32Def; infer_instance
instance ownUint32_dfractional (u : Loc) (v : w32) :
    DFractional (fun dq => ownUint32 (GF := GF) u dq v) := by
  rw [ownUint32_unseal]; unfold ownUint32Def; infer_instance
instance ownUint32_as_dfractional (u : Loc) (v : w32) (dq : DFrac) :
    AsDFractional (ownUint32 (GF := GF) u dq v) (fun dq => ownUint32 u dq v) dq :=
  ⟨.rfl, ownUint32_dfractional u v⟩
instance ownUint32_fractional (u : Loc) (v : w32) :
    Fractional (fun q => ownUint32 (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => ownUint32 (GF := GF) u dq v)
instance ownUint32_combines_gives (u : Loc) (v v' : w32) (dq dq' : DFrac) :
    CombineSepGives (ownUint32 (GF := GF) u dq v) (ownUint32 u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [ownUint32_unseal]; unfold ownUint32Def
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    cases Heq; rfl

theorem Uint32.wp_Load (u : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w32, ownUint32 u dq v ∗ (ownUint32 u dq v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.GoType.PointerType Uint32.ty @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [ownUint32_unseal, ownUint32Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Uint32.wp_Store (u : Loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w32, ownUint32 u (DFrac.own 1) old ∗
        (ownUint32 u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (u @!! go.GoType.PointerType Uint32.ty @!! go!"Store")) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_StoreUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownUint32_unseal, ownUint32Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Uint32.wp_Add (u : Loc) (delta : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w32, ownUint32 u (DFrac.own 1) old ∗
        (ownUint32 u (DFrac.own 1) (old + delta) ={∅,⊤}=∗ Φ #(old + delta))) -∗
      WP (App (Val (u @!! go.GoType.PointerType Uint32.ty @!! go!"Add")) (Val #delta)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_AddUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownUint32_unseal, ownUint32Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Uint32.wp_CompareAndSwap (u : Loc) (old new : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w32) (dq : DFrac), ownUint32 u dq v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (ownUint32 u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (Val (u @!! go.GoType.PointerType Uint32.ty @!! go!"CompareAndSwap")) (Val #old))
        (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_CompareAndSwapUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [ownUint32_unseal, ownUint32Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v, dq
  iframe v
  isplitr
  · ipureintro; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

/-! ### Int32 -/

theorem wp_LoadInt32 (addr : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w32, addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (@! LoadInt32)) (Val #addr)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%v, >Haddr, HΦ⟩
  wp_apply_core wp_word_load addr dq v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_SwapInt32 (addr : Loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w32, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
      WP (App (App (Val (@! SwapInt32)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_word_swap addr oldv v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_StoreInt32 (addr : Loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w32, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! StoreInt32)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_bind (AtomicWord _ _ _ _)
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_word_swap addr oldv v $$ Haddr
  iintro Haddr
  imod HΦ $$ Haddr with HΦ
  imodintro
  wp_pures
  iexact HΦ

theorem wp_AddInt32 (addr : Loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : w32, addr ↦ oldv ∗
        (addr ↦ (oldv + v) ={∅,⊤}=∗ Φ #(oldv + v))) -∗
      WP (App (App (Val (@! AddInt32)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_word_add addr oldv v (oldv + v) (toZ_add_w32 oldv v) $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_CompareAndSwapInt32 (addr : Loc) (old new : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w32) (dq : DFrac), addr ↦{dq} v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (addr ↦{dq} (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (App (Val (@! CompareAndSwapInt32)) (Val #addr)) (Val #old)) (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_bind (AtomicWord _ _ _ _)
  imod HΦ with ⟨%v, %dq, >Haddr, >%Hdq, HΦ⟩
  by_cases h : v = old
  · subst h
    simp only [↓reduceIte, decide_true] at Hdq ⊢
    subst Hdq
    wp_apply_core wp_word_cmpxchg_suc addr v v new rfl $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ
  · simp only [h, ↓reduceIte, decide_false]
    wp_apply_core wp_word_cmpxchg_fail addr dq v old new h $$ Haddr
    iintro Haddr
    imod HΦ $$ Haddr with HΦ
    imodintro
    wp_pures
    iexact HΦ

def ownInt32Def (u : Loc) (dq : DFrac) (v : w32) : IProp GF :=
  typedPointsto (GF := GF) u ({ _0' := zero_val _, v' := v : Int32 }) dq
@[irreducible] def ownInt32 (u : Loc) (dq : DFrac) (v : w32) : IProp GF := ownInt32Def u dq v
theorem ownInt32_unseal : @ownInt32 = @ownInt32Def := by funext; with_unfolding_all rfl

instance ownInt32_timeless (u : Loc) (dq : DFrac) (v : w32) :
    Timeless (ownInt32 (GF := GF) u dq v) := by
  rw [ownInt32_unseal]; unfold ownInt32Def; infer_instance
instance ownInt32_dfractional (u : Loc) (v : w32) :
    DFractional (fun dq => ownInt32 (GF := GF) u dq v) := by
  rw [ownInt32_unseal]; unfold ownInt32Def; infer_instance
instance ownInt32_as_dfractional (u : Loc) (v : w32) (dq : DFrac) :
    AsDFractional (ownInt32 (GF := GF) u dq v) (fun dq => ownInt32 u dq v) dq :=
  ⟨.rfl, ownInt32_dfractional u v⟩
instance ownInt32_fractional (u : Loc) (v : w32) :
    Fractional (fun q => ownInt32 (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => ownInt32 (GF := GF) u dq v)
instance ownInt32_combines_gives (u : Loc) (v v' : w32) (dq dq' : DFrac) :
    CombineSepGives (ownInt32 (GF := GF) u dq v) (ownInt32 u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [ownInt32_unseal]; unfold ownInt32Def
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    cases Heq; rfl

theorem Int32.wp_Load (u : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : w32, ownInt32 u dq v ∗ (ownInt32 u dq v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.GoType.PointerType Int32.ty @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadInt32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [ownInt32_unseal, ownInt32Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Int32.wp_Store (u : Loc) (v : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w32, ownInt32 u (DFrac.own 1) old ∗
        (ownInt32 u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (u @!! go.GoType.PointerType Int32.ty @!! go!"Store")) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_StoreInt32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownInt32_unseal, ownInt32Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Int32.wp_Add (u : Loc) (delta : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : w32, ownInt32 u (DFrac.own 1) old ∗
        (ownInt32 u (DFrac.own 1) (old + delta) ={∅,⊤}=∗ Φ #(old + delta))) -∗
      WP (App (Val (u @!! go.GoType.PointerType Int32.ty @!! go!"Add")) (Val #delta)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_AddInt32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownInt32_unseal, ownInt32Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Int32.wp_CompareAndSwap (u : Loc) (old new : w32) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : w32) (dq : DFrac), ownInt32 u dq v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (ownInt32 u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (Val (u @!! go.GoType.PointerType Int32.ty @!! go!"CompareAndSwap")) (Val #old))
        (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_CompareAndSwapInt32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [ownInt32_unseal, ownInt32Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v, dq
  iframe v
  isplitr
  · ipureintro; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

/-! ### Pointer -/

theorem wp_LoadPointer (addr : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : Loc, addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (@! LoadPointer)) (Val #addr)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%v, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_load _ _ addr dq v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_SwapPointer (addr : Loc) (v : Loc) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : Loc, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
      WP (App (App (Val (@! SwapPointer)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core wp_atomic_swap _ _ addr oldv v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

theorem wp_StorePointer (addr : Loc) (v : Loc) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ oldv : Loc, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
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

theorem wp_CompareAndSwapPointer (addr : Loc) (old new : Loc) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : Loc) (dq : DFrac), addr ↦{dq} v ∗
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
variable {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType) [IntoValTyped (GF := GF) T' T]

def ownPointerDef (u : Loc) (dq : DFrac) (v : Loc) : IProp GF :=
  typedPointsto (GF := GF) u ({ _0' := zero_val _, _1' := zero_val _, v' := v } : Pointer T') dq
@[irreducible] def ownPointer (u : Loc) (dq : DFrac) (v : Loc) : IProp GF :=
  ownPointerDef (T' := T') u dq v
theorem ownPointer_unseal : @ownPointer = @ownPointerDef := by funext; with_unfolding_all rfl

instance ownPointer_timeless (u : Loc) (dq : DFrac) (v : Loc) :
    Timeless (ownPointer (GF := GF) (T' := T') u dq v) := by
  rw [ownPointer_unseal]; unfold ownPointerDef; infer_instance

theorem Pointer.wp_Load (u : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : Loc, ownPointer (T' := T') u dq v ∗ (ownPointer (T' := T') u dq v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.GoType.PointerType (Pointer.ty T) @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadPointer $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [ownPointer_unseal, ownPointerDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Pointer.wp_Store (u : Loc) (v : Loc) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : Loc, ownPointer (T' := T') u (DFrac.own 1) old ∗
        (ownPointer (T' := T') u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (u @!! go.GoType.PointerType (Pointer.ty T) @!! go!"Store")) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_StorePointer $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownPointer_unseal, ownPointerDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Pointer.wp_CompareAndSwap (u : Loc) (old new : Loc) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : Loc) (dq : DFrac), ownPointer (T' := T') u dq v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (ownPointer (T' := T') u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (Val (u @!! go.GoType.PointerType (Pointer.ty T) @!! go!"CompareAndSwap")) (Val #old))
        (Val #new)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_CompareAndSwapPointer $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [ownPointer_unseal, ownPointerDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v, dq
  iframe v
  isplitr
  · ipureintro; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Pointer.wp_Swap (u : Loc) (v' : Loc) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ∃ v : Loc, ownPointer (T' := T') u (DFrac.own 1) v ∗
        (ownPointer (T' := T') u (DFrac.own 1) v' ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.GoType.PointerType (Pointer.ty T) @!! go!"Swap")) (Val #v')) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_SwapPointer $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [ownPointer_unseal, ownPointerDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

end pointer

/-! ### Bool -/

/-- The `w32` encoding of a Boolean (not named `b32`: `sync.atomic.b32` is the Go
function's name). -/
def b32w (b : Bool) : w32 := if b then W32 1 else W32 0

theorem b32w_inj {b1 b2 : Bool} (h : b32w b1 = b32w b2) : b1 = b2 := by
  cases b1 <;> cases b2 <;> first | rfl | (exfalso; revert h; decide)

def ownBoolDef (u : Loc) (dq : DFrac) (v : Bool) : IProp GF :=
  typedPointsto (GF := GF) u ({ _0' := zero_val _, v' := b32w v } : Bool') dq
@[irreducible] def ownBool (u : Loc) (dq : DFrac) (v : Bool) : IProp GF := ownBoolDef u dq v
theorem ownBool_unseal : @ownBool = @ownBoolDef := by funext; with_unfolding_all rfl

instance ownBool_timeless (u : Loc) (dq : DFrac) (v : Bool) :
    Timeless (ownBool (GF := GF) u dq v) := by
  rw [ownBool_unseal]; unfold ownBoolDef; infer_instance
instance ownBool_dfractional (u : Loc) (v : Bool) :
    DFractional (fun dq => ownBool (GF := GF) u dq v) := by
  rw [ownBool_unseal]; unfold ownBoolDef; infer_instance
instance ownBool_fractional (u : Loc) (v : Bool) :
    Fractional (fun q => ownBool (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => ownBool (GF := GF) u dq v)
instance ownBool_as_fractional (u : Loc) (q : Qp) (v : Bool) :
    AsFractional (ownBool (GF := GF) u (DFrac.own q) v) ioΦ
      (fun q => ownBool u (DFrac.own q) v) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := ownBool_fractional u v
instance ownBool_combines_gives (u : Loc) (v v' : Bool) (dq dq' : DFrac) :
    CombineSepGives (ownBool (GF := GF) u dq v) (ownBool u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [ownBool_unseal]; unfold ownBoolDef
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    exact b32w_inj (congrArg Bool'.v' Heq)

theorem Bool.wp_Load (u : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ v : Bool, ownBool u dq v ∗ (ownBool u dq v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (u @!! go.GoType.PointerType Bool'.ty @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [ownBool_unseal, ownBoolDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists (b32w v)
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  cases v <;> simp [b32w] <;> iexact HΦ

theorem wp_b32 (b : Bool) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      Φ #(b32w b) -∗ WP (App (Val (@! b32)) (Val #b)) {{ Φ }} := by
  wp_start as _
  cases b <;> simp only [b32w, Bool.false_eq_true, ↓reduceIte] <;> wp_auto <;> iexact HΦ

theorem Bool.wp_Store (u : Loc) (v : Bool) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ old : Bool, ownBool u (DFrac.own 1) old ∗
        (ownBool u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (u @!! go.GoType.PointerType Bool'.ty @!! go!"Store")) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply wp_b32
  wp_apply_core wp_StoreUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownBool_unseal, ownBoolDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists (b32w old)
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

theorem Bool.wp_CompareAndSwap (u : Loc) (old new : Bool) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ (v : Bool) (dq : DFrac), ownBool u dq v ∗
        ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
        (ownBool u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
      WP (App (App (Val (u @!! go.GoType.PointerType Bool'.ty @!! go!"CompareAndSwap")) (Val #old))
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
  simp only [ownBool_unseal, ownBoolDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  have hiff : (b32w v = b32w old) ↔ (v = old) := ⟨b32w_inj, fun h => h ▸ rfl⟩
  iexists (b32w v), dq
  iframe v
  isplitr
  · ipureintro; simp only [hiff]; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
    by_cases h : v = old <;> simp [h, hiff]
    · iexact Hv
    · iexact Hv
  imodintro
  wp_auto
  simp only [decide_eq_decide.mpr hiff]
  iexact HΦ
/-! ### Value

`Value` is a trusted model (`Perennial/TrustedCode/sync/atomic.lean`): an atomic
cell holding an `any`. `Store`/`Swap`/`CompareAndSwap` may panic (in the model)
when the cell is non-empty, since the model cannot check Go's "consistently
typed" requirement; so their specs require the cell to be empty (`nil`) at the
linearization point. -/

instance : Inhabited GoInterface := ⟨interface.nil⟩

instance atomic_wps_interface : AtomicWps (GF := GF) GoInterface := by solve_atomic_wps

def ownValueDef (u : Loc) (dq : DFrac) (x : GoInterface) : IProp GF :=
  typedPointsto (GF := GF) u (x : Value) dq
@[irreducible] def ownValue (u : Loc) (dq : DFrac) (x : GoInterface) : IProp GF :=
  ownValueDef u dq x
theorem ownValue_unseal : @ownValue = @ownValueDef := by funext; with_unfolding_all rfl

instance ownValue_timeless (u : Loc) (dq : DFrac) (x : GoInterface) :
    Timeless (ownValue (GF := GF) u dq x) := by
  rw [ownValue_unseal]; unfold ownValueDef; infer_instance
instance ownValue_dfractional (u : Loc) (x : GoInterface) :
    DFractional (fun dq => ownValue (GF := GF) u dq x) := by
  rw [ownValue_unseal]; unfold ownValueDef; infer_instance
instance ownValue_fractional (u : Loc) (x : GoInterface) :
    Fractional (fun q => ownValue (GF := GF) u (DFrac.own q) x) :=
  fractional_of_dfractional (fun dq => ownValue (GF := GF) u dq x)
instance ownValue_as_fractional (u : Loc) (q : Qp) (x : GoInterface) :
    AsFractional (ownValue (GF := GF) u (DFrac.own q) x) ioΦ
      (fun q => ownValue u (DFrac.own q) x) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := ownValue_fractional u x
instance ownValue_combines_gives (u : Loc) (x x' : GoInterface) (dq dq' : DFrac) :
    CombineSepGives (ownValue (GF := GF) u dq x) (ownValue u dq' x') iprop(⌜x = x'⌝) where
  combine_sep_gives := by
    rw [ownValue_unseal]; unfold ownValueDef
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro; exact Heq

/-- A zero `Value` (as in a freshly allocated struct) is an empty cell. -/
theorem ownValue_zero (u : Loc) (dq : DFrac) :
    typedPointsto (GF := GF) u (zero_val Value) dq ⊣⊢ ownValue u dq interface.nil := by
  rw [ownValue_unseal]; exact .rfl

theorem Value.wp_Load (u : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ ∃ x : GoInterface, ownValue u dq x ∗ (ownValue u dq x ={∅,⊤}=∗ Φ #x)) -∗
      WP (App (Val (u @!! go.GoType.PointerType Value.ty @!! go!"Load")) (Val #())) {{ Φ }} := by
  wp_start as _
  imod HΦ with ⟨%x, >Hown, HΦ⟩
  simp only [ownValue_unseal, ownValueDef]
  wp_apply_core wp_atomic_load _ _ u dq (x : GoInterface) $$ Hown
  iintro Hown
  iapply HΦ $$ Hown

theorem Value.wp_Store (u : Loc) (v : GoInterface) (hv : v ≠ interface.nil) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ (ownValue u (DFrac.own 1) interface.nil ∗
        (ownValue u (DFrac.own 1) v ={∅,⊤}=∗ Φ #()))) -∗
      WP (App (Val (u @!! go.GoType.PointerType Value.ty @!! go!"Store")) (Val #v)) {{ Φ }} := by
  wp_start as _
  cases v with
  | nil => exact absurd rfl hv
  | ok ii =>
  simp only
  wp_auto
  wp_bind (AtomicSwap _ _)
  imod HΦ with ⟨>Hown, HΦ⟩
  simp only [ownValue_unseal, ownValueDef]
  wp_apply_core wp_atomic_swap _ _ u (interface.nil : GoInterface) (interface.ok ii) $$ Hown
  iintro Hown
  imod HΦ $$ Hown with HΦ
  imodintro
  wp_auto
  iexact HΦ

theorem Value.wp_Swap (u : Loc) (v : GoInterface) (hv : v ≠ interface.nil) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|={⊤,∅}=> ▷ (ownValue u (DFrac.own 1) interface.nil ∗
        (ownValue u (DFrac.own 1) v ={∅,⊤}=∗ Φ #interface.nil))) -∗
      WP (App (Val (u @!! go.GoType.PointerType Value.ty @!! go!"Swap")) (Val #v)) {{ Φ }} := by
  wp_start as _
  cases v with
  | nil => exact absurd rfl hv
  | ok ii =>
  simp only
  wp_auto
  wp_bind (AtomicSwap _ _)
  imod HΦ with ⟨>Hown, HΦ⟩
  simp only [ownValue_unseal, ownValueDef]
  wp_apply_core wp_atomic_swap _ _ u (interface.nil : GoInterface) (interface.ok ii) $$ Hown
  iintro Hown
  imod HΦ $$ Hown with HΦ
  imodintro
  wp_auto
  iexact HΦ

/-- `CompareAndSwap(nil, new)` on an empty cell owned by the caller; it may fail
spuriously (see the model). -/
theorem Value.wp_CompareAndSwap (u : Loc) (new : GoInterface) (hnew : new ≠ interface.nil) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ ownValue u (DFrac.own 1) interface.nil }}
      (App (App (Val (u @!! go.GoType.PointerType Value.ty @!! go!"CompareAndSwap"))
        (Val #interface.nil)) (Val #new))
    {{ (b : Bool), RET #b; ownValue u (DFrac.own 1) (if b then new else interface.nil) }} := by
  wp_start as Hown
  cases new with
  | nil => exact absurd rfl hnew
  | ok ii =>
  simp only
  wp_auto
  simp only [ownValue_unseal, ownValueDef]
  wp_bind (Load _)
  wp_apply_core wp_atomic_load _ _ u (DFrac.own 1) (interface.nil : GoInterface) $$ Hown
  iintro Hown
  wp_auto
  wp_bind ArbitraryInt
  wp_apply_core wp_ArbitraryInt
  iintro %x _
  wp_auto
  by_cases hx : x = W64 0
  · subst hx
    wp_auto
    wp_bind (CmpXchg _ _ _)
    wp_apply_core wp_cmpxchg_suc u (interface.nil : GoInterface) interface.nil (interface.ok ii) _ _ rfl $$ Hown
    iintro Hown
    wp_auto
    iapply HΦ
    simp only [↓reduceIte, Bool.false_eq_true]
    iexact Hown
  · simp only [hx, decide_false]
    wp_auto
    iapply HΦ
    simp only [↓reduceIte, Bool.false_eq_true]
    iexact Hown

end wps

end sync.atomic

end Perennial
end
