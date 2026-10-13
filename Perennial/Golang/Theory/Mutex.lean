/-
The program logic of `go.mutex` (`Golang/Defn/Mutex.lean`).
-/
module

public import Perennial.Golang.Theory.Auto

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

/-! ### `go.mutex`: a lock laid out as gc's `sync.Mutex`

The typed points-to of a `MutexState` is its lock's, the `bool` in its first cell
(`go.MutexSemantics`); the other cells of its 8 are not owned. -/

section mutex
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics]

instance typedPointsto_mutex : TypedPointsto (GF := GF) MutexState where
  typedPointstoDef l m dq := typedPointstoDef (GF := GF) (V := Bool) l m.locked dq
  typedPointstoDef_dfractional l m := typedPointstoDef_dfractional (GF := GF) (V := Bool) l m.locked
  typedPointstoDef_timeless l m dq := typedPointstoDef_timeless (GF := GF) (V := Bool) l m.locked dq
  typedPointsto_agree l dq1 dq2 m1 m2 := by
    obtain ⟨b1⟩ := m1; obtain ⟨b2⟩ := m2
    iintro H1 H2
    ihave %h := typedPointsto_agree (GF := GF) (V := Bool) l dq1 dq2 b1 b2 $$ H1 H2
    ipureintro; rw [h]

@[simp] theorem MutexState.zero_locked : (zero_val MutexState).locked = false := rfl

theorem typedPointsto_mutex_eq (l : Loc) (m : MutexState) (dq : DFrac) :
    typedPointsto (GF := GF) l m dq = typedPointsto (GF := GF) l m.locked dq := by
  rw [typedPointsto_unseal]; rfl

instance intoVal_typed_mutex : IntoValTypedUnderlying (GF := GF) MutexState go.mutex where
  wp_alloc_def {s E t} _ v := by
    obtain ⟨b⟩ := v
    have hstore : ∀ l : Loc, {{ (⌜l.locCar ≠ 0⌝ ∗ rawCells l 8 : IProp GF) }}
        (App (Val (GoInstruction (GoStore go.bool))) (Val (PairV #l #b))) @ s; E
        {{ RET #(); typedPointsto (GF := GF) l b (DFrac.own 1) }} := by
      intro l
      iintro %Ψ ⟨%Hc, Hraw⟩ HΨ
      ihave Hraw := rawCells_le l 1 8 (by decide) (by decide) $$ Hraw
      iapply IntoValTyped.wp_store_raw (t := go.bool) l b $$ [Hraw] HΨ
      rw [go.typeSize_bool]
      iframe Hraw
      ipureintro; exact Hc
    iintro %Φ _ HΦ
    have hpw : PureWp (hlc := hlc) (GF := GF) True
        (App (Val (GoInstruction (GoAlloc t))) (Val #(MutexState.mk b)))
        (Let "l" (AllocN (Val (PairV (LitV (LitInt (W64 8))) (LitV (LitInt (W64 4)))))
            (Val (LitV LitPad)))
          gl(GoStore go.bool ("l", #(MutexState.mk b)) ;; "l") : Expr) := by
      have _tagged := @go.tagged_internal_inst
      infer_instance
    iapply (wp_pure_raw_step (Hwp := hpw) trivial)
    inext
    rw [go.mutex_val]
    iapply (wp_alloc_raw go.bool 8 4 (by decide) (by decide) #b
      (fun l => typedPointsto (GF := GF) l b (DFrac.own 1)) hstore) $$ []
    · itrivial
    inext
    iintro %l ⟨Hl, %Hal⟩
    iapply HΦ
    rw [typedPointsto_mutex_eq]
    iframe Hl
    ipureintro
    exact ⟨Hal.1, by rw [go.typeAlign_mutex]; exact Hal.2⟩
  wp_load_def {s E t} _ l dq v := by
    obtain ⟨b⟩ := v
    iintro %Φ Hl HΦ
    simp only [typedPointsto_mutex_eq]
    have hpw : PureWp (hlc := hlc) (GF := GF) True
        (App (Val (GoInstruction (GoLoad t))) (Val #l))
        (App (Val (GoInstruction (GoLoad go.bool))) (Val #l)) := by
      have _tagged := @go.tagged_internal_inst
      infer_instance
    iapply (wp_pure_raw_step (Hwp := hpw) trivial)
    inext
    iapply IntoValTyped.wp_load (t := go.bool) l dq b $$ Hl
    inext
    iintro Hl
    rw [go.mutex_val]
    iapply HΦ $$ Hl
  wp_store_def {s E t} _ l v w := by
    obtain ⟨b⟩ := v; obtain ⟨c⟩ := w
    iintro %Φ Hl HΦ
    simp only [typedPointsto_mutex_eq]
    rw [go.mutex_val]
    have hpw : PureWp (hlc := hlc) (GF := GF) True
        (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #c)))
        (App (Val (GoInstruction (GoStore go.bool))) (Val (PairV #l #c))) := by
      have _tagged := @go.tagged_internal_inst
      infer_instance
    iapply (wp_pure_raw_step (Hwp := hpw) trivial)
    inext
    iapply IntoValTyped.wp_store (t := go.bool) l b c $$ Hl
    inext
    iintro Hl
    iapply HΦ $$ Hl
  wp_store_raw_def {s E t} _ l w := by
    obtain ⟨c⟩ := w
    iintro %Φ ⟨%Hc, Hraw⟩ HΦ
    rw [typedPointsto_mutex_eq, go.mutex_val]
    rw [go.typeSize_mutex] at *
    ihave Hraw := rawCells_le l 1 8 (by decide) (by decide) $$ Hraw
    rw [← go.typeSize_bool] at *
    have hpw : PureWp (hlc := hlc) (GF := GF) True
        (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #c)))
        (App (Val (GoInstruction (GoStore go.bool))) (Val (PairV #l #c))) := by
      have _tagged := @go.tagged_internal_inst
      infer_instance
    iapply (wp_pure_raw_step (Hwp := hpw) trivial)
    inext
    iapply IntoValTyped.wp_store_raw (t := go.bool) l c $$ [Hraw] HΦ
    iframe Hraw
    ipureintro; exact Hc
  type_repr_def := go.type_repr_mutex

end mutex

end Perennial
