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

A `MutexState` is one `Encoding.cell 8` value whose head is its lock's `bool`
(`go.MutexSemantics.mutex_val`); `typedPointsto_mutex_lock` gives the lock's cell. -/

section mutex
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics]

include hG pre_sem in
theorem mutex_intoVal_inj : Function.Injective (intoVal (V := MutexState)) := by
  intro ⟨a⟩ ⟨b⟩ h
  rw [go.mutex_val, go.mutex_val] at h
  rw [GoGlobalContext.intoVal_inj_bool h]

include hG pre_sem in
theorem encode_mutex (m : MutexState) :
    encode (.cell 8) #m = some (#m.locked :: tails 8) := by
  obtain ⟨b⟩ := m
  rw [go.mutex_val]
  have h : CellHeadOf 8 #b := ⟨by omega, CellHeadType.head b, fun h => by omega⟩
  simp only [encode, if_pos h]

instance typedPointsto_mutex : TypedPointsto (GF := GF) MutexState :=
  encTypedPointsto MutexState (.cell 8) (mutex_intoVal_inj (hG := hG))
    (fun m => ⟨_, encode_mutex (hG := hG) m⟩)

@[simp] theorem MutexState.zero_locked : (zero_val MutexState).locked = false := rfl

theorem typedPointsto_mutex_unfold (l : Loc) (m : MutexState) (dq : DFrac) :
    typedPointsto (GF := GF) l m dq =
      iprop(pointstoVals l dq (#m.locked :: tails 8) ∗ ⌜l ≠ null⌝) := by
  rw [typedPointsto_unseal_eq]
  show iprop(pointstoVals l dq (encodeVals (.cell 8) #m) ∗ ⌜l ≠ null⌝) = _
  rw [encodeVals_eq (encode_mutex (hG := hG) m)]

/-- The lock of a mutex: the `bool` in its first cell. -/
theorem typedPointsto_mutex_lock (l : Loc) (m : MutexState) (dq : DFrac) :
    typedPointsto (GF := GF) l m dq ⊢ typedPointsto (GF := GF) l m.locked dq := by
  rw [typedPointsto_mutex_unfold, typedPointsto_unseal_eq]
  iintro ⟨H, %Hnn⟩
  unfold pointstoVals
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H0, -⟩
  isplitl [H0]
  · iapply (typedPointstoDef_bool l m.locked dq).2
    rw [encodeVals_eq (encode_bool (hG := hG) m.locked)]
    iapply (pointstoVals_single l dq _).2
    simp only [Int.natCast_zero, loc_add_0]
    iexact H0
  · ipureintro; exact Hnn

instance intoVal_typed_mutex : IntoValTypedUnderlying (GF := GF) MutexState go.mutex where
  wp_alloc_def {s E t} _ v := by
    iintro %Φ _ HΦ
    have hpw : PureWp (hlc := hlc) (GF := GF) True
        (App (Val (GoInstruction (GoAlloc t))) (Val #v))
        (Let "l" (AllocN (Val (PairV (LitV (LitInt (W64 8))) (LitV (LitInt (W64 4)))))
            (Val (LitV LitPad)))
          (Seq (App (App (Val (StoreN (.cell 8))) (Var "l")) (Val #v)) (Var "l"))) := by
      have _tagged := @go.tagged_internal_inst
      infer_instance
    iapply (wp_pure_raw_step (Hwp := hpw) trivial)
    inext
    wp_apply_core wp_allocN _ _ _
    iintro %l ⟨%Hoff, Hl⟩
    wp_pures
    wp_apply_core wp_StoreN (.cell 8) l _ _ #v (by simp [Encoding.size])
      (by simp) (writeCompat_pads _ _) (encode_mutex (hG := hG) v) $$ Hl
    iintro Hl
    wp_pures
    iapply HΦ
    rw [typedPointsto_mutex_unfold]
    iframe Hl
    ipureintro
    refine ⟨fun h => by subst h; exact Hoff.1 rfl, Hoff.1, ?_⟩
    rw [go.typeAlign_mutex]
    have := Hoff.2
    rwa [show ((uint.nat (W64 4) : Nat) : Int) = 4 from rfl] at this
  wp_load_def {s E t} _ l dq v := by
    iintro %Φ Hl HΦ
    rw [typedPointsto_mutex_unfold]
    icases Hl with ⟨Hl, %Hnn⟩
    have hpw : PureWp (hlc := hlc) (GF := GF) True
        (App (Val (GoInstruction (GoLoad t))) (Val #l))
        (App (Val (ReadN (.cell 8))) (Val #l)) := by
      have _tagged := @go.tagged_internal_inst
      infer_instance
    iapply (wp_pure_raw_step (Hwp := hpw) trivial)
    inext
    have hdec : decode (.cell 8) (#v.locked :: tails 8) = some #v := by
      have := decode_encode (encode_mutex (hG := hG) v); exact this
    wp_apply_core wp_ReadN (.cell 8) l dq _ #v (by simp [Encoding.size, tails]) hdec $$ Hl
    iintro Hl
    iapply HΦ
    iframe Hl
    ipureintro; exact Hnn
  wp_store_def {s E t} _ l v w := by
    iintro %Φ Hl HΦ
    simp only [typedPointsto_mutex_unfold]
    icases Hl with ⟨Hl, %Hnn⟩
    have hpw : PureWp (hlc := hlc) (GF := GF) True
        (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w)))
        (App (App (Val (StoreN (.cell 8))) (Val #l)) (Val #w)) := by
      have _tagged := @go.tagged_internal_inst
      infer_instance
    iapply (wp_pure_raw_step (Hwp := hpw) trivial)
    inext
    wp_apply_core wp_StoreN (.cell 8) l _ _ #w (by simp [Encoding.size, tails])
      (by simp) (encode_writeCompat (encode_mutex (hG := hG) v)) (encode_mutex (hG := hG) w) $$ Hl
    iintro Hl
    iapply HΦ
    iframe Hl
    ipureintro; exact Hnn
  wp_store_raw_def {s E t} _ l w := by
    iintro %Φ ⟨%Hc, Hraw⟩ HΦ
    rw [go.typeSize_mutex]
    ihave Hl := rawCells_vals' l 8 8 rfl $$ Hraw
    have hpw : PureWp (hlc := hlc) (GF := GF) True
        (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w)))
        (App (App (Val (StoreN (.cell 8))) (Val #l)) (Val #w)) := by
      have _tagged := @go.tagged_internal_inst
      infer_instance
    iapply (wp_pure_raw_step (Hwp := hpw) trivial)
    inext
    wp_apply_core wp_StoreN (.cell 8) l _ _ #w (by simp [Encoding.size])
      (by simp) (writeCompat_pads _ _) (encode_mutex (hG := hG) w) $$ Hl
    iintro Hl
    iapply HΦ
    rw [typedPointsto_mutex_unfold]
    iframe Hl
    ipureintro; intro h; subst h; exact Hc rfl
  type_repr_def := go.type_repr_mutex

end mutex

end Perennial
