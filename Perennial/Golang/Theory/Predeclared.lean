/-
`IntoValTypedUnderlying` instances
for the predeclared Go types (integers, including `uintptr`, `bool`,
`string`, `unsafe.Pointer`, floats, `proph_id`).
-/
module

public import Perennial.Golang.Theory.PostLifting

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section into_val_typed_instances
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

attribute [local instance] go.tagged_internal_inst

section plain_scalar
variable {s : Stuckness} {E : CoPset}
open ProofMode

@[simp] theorem bytesTuple_isPanic (bs : List w8) : (go.bytesTuple bs).isPanic = false := by
  cases bs <;> rfl

theorem wp_readBytes (l : Loc) (dq : DFrac) (bs : List w8) (Φ : val → IProp GF) :
    bytesPointsto (GF := GF) l dq bs -∗ (bytesPointsto l dq bs -∗ Φ (go.bytesTuple bs)) -∗
      WP (go.readBytes l bs.length) @ s; E {{ Φ }} := by
  induction bs generalizing l Φ with
  | nil =>
    simp only [go.readBytes, go.bytesTuple, List.length_nil]
    iintro Hbs HΦ
    wp_pures
    iapply HΦ $$ Hbs
  | cons b bs ih =>
    simp only [go.readBytes, go.bytesTuple, List.length_cons, bytesPointsto]
    iintro ⟨Hb, Hbs⟩ HΦ
    wp_apply_core _internal_wp_untyped_read l dq _ rfl $$ Hb
    iintro Hb
    wp_apply_core ih (l +ₗ 1) $$ Hbs
    iintro Hbs
    wp_pures
    simp only [go.intoVal_unfold w8]
    iapply HΦ
    iframe

theorem wp_writeBytes (l : Loc) (bs bs' : List w8) (hlen : bs'.length = bs.length)
    (Φ : val → IProp GF) :
    bytesPointsto (GF := GF) l (.own 1) bs -∗ (bytesPointsto l (.own 1) bs' -∗ Φ #()) -∗
      WP (go.writeBytes l bs') @ s; E {{ Φ }} := by
  induction bs generalizing l bs' with
  | nil =>
    cases bs' with
    | nil =>
      simp only [go.writeBytes]
      iintro Hbs HΦ
      wp_pures
      iapply HΦ $$ Hbs
    | cons => simp at hlen
  | cons b bs ih =>
    cases bs' with
    | nil => simp at hlen
    | cons b' bs' =>
      simp only [go.writeBytes, bytesPointsto]
      iintro ⟨Hb, Hbs⟩ HΦ
      wp_apply_core _internal_wp_untyped_store l _ #b' (by rw [go.intoVal_unfold w8]; rfl) $$ Hb
      iintro Hb
      wp_pures
      wp_apply_core ih (l +ₗ 1) bs' (by simpa using hlen) $$ Hbs
      iintro Hbs
      iapply HΦ
      simp only [go.intoVal_unfold w8]
      iframe

theorem wp_alloc_plain_scalar (w : Nat) {t t_under : go.GoType} [go.IsUnderlying t t_under]
    [go.IsPlainScalar t_under w] (v : val) (bs : List w8) (hv : valBytes w v = some bs) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoAlloc t))) (Val v)) @ s; E
    {{ l, RET #l; bytesPointsto l (.own 1) bs ∗ ⌜l ≠ null⌝ }} := by
  have := valBytes_not_panic hv
  iintro %Φ _ HΦ
  wp_pures
  wp_apply_core wp_alloc_bytes w v bs hv
  iintro %l Hbs
  have hne : bs ≠ [] := by
    intro h; have := valBytes_length hv; have := valBytes_pos hv; subst h; simp at *; omega
  icases bytesPointsto_non_null l _ bs hne $$ Hbs with ⟨Hbs, %Hnn⟩
  iapply HΦ
  iframe Hbs
  ipureintro; assumption

theorem wp_load_plain_scalar (w : Nat) {t t_under : go.GoType} [go.IsUnderlying t t_under]
    [go.IsPlainScalar t_under w] (l : Loc) (dq : DFrac) (bs : List w8) (v : val)
    (hlen : bs.length = w) (hv : bytesVal w bs = some v) :
    {{ bytesPointsto (GF := GF) l dq bs }} (App (Val (GoInstruction (GoLoad t))) (Val #l)) @ s; E
    {{ RET v; bytesPointsto l dq bs }} := by
  subst hlen
  haveI := go.bytes_to bs.length bs v hv
  iintro %Φ Hbs HΦ
  wp_pures
  wp_apply_core wp_readBytes l dq bs $$ Hbs
  iintro Hbs
  wp_pures
  iapply HΦ $$ Hbs

theorem wp_store_plain_scalar (w : Nat) {t t_under : go.GoType} [go.IsUnderlying t t_under]
    [go.IsPlainScalar t_under w] (l : Loc) (bs bs' : List w8) (v0 v' : val)
    (hlen : bs.length = w) (hv0 : bytesVal w bs = some v0) (hv' : valBytes w v' = some bs') :
    {{ bytesPointsto (GF := GF) l (.own 1) bs }}
      (App (Val (GoInstruction (GoStore t))) (Val (PairV #l v'))) @ s; E
    {{ RET #(); bytesPointsto l (.own 1) bs' }} := by
  have hlen' : bs'.length = bs.length := by rw [valBytes_length hv', hlen]
  subst hlen
  have := bytesVal_not_panic hv0
  haveI := go.bytes_to bs.length bs v0 hv0
  iintro %Φ Hbs HΦ
  wp_pures
  simp only [hv']
  wp_apply_core wp_readBytes l (.own 1) bs $$ Hbs
  iintro Hbs
  wp_pures
  wp_apply_core wp_writeBytes l bs bs' hlen' $$ Hbs
  iintro Hbs
  iapply HΦ $$ Hbs

theorem bytesPointsto_singleton (l : Loc) (dq : DFrac) (b : w8) :
    bytesPointsto (GF := GF) l dq [b] ⊣⊢ heapPointsto (GF := GF) l dq #b := by
  simp only [go.intoVal_unfold w8, bytesPointsto]
  constructor
  · iintro ⟨H, _⟩; iexact H
  · iintro H; iframe H


end plain_scalar

/-- Prove `IntoValTypedUnderlying w8 t` for a plain scalar type `t` of 1 byte, whose typed
points-to is the heap points-to of its byte. -/
macro "solve_into_val_typed_byte" : tactic => `(tactic| (
  constructor
  all_goals try simp only [typedPointsto_unseal, typedPointstoWrap, typedPointstoDef_heap]
  · intro s E t _ v
    iintro %Φ _ HΦ
    wp_apply_core wp_alloc_plain_scalar _ #v [v]
      (by rw [go.intoVal_unfold w8]; simp [valBytes, natBytes])
    iintro %l ⟨Hbs, %Hnn⟩
    icases (bytesPointsto_singleton l _ v).1 $$ Hbs with Hb
    iapply HΦ
    iframe Hb
    ipureintro; assumption
  · intro s E t _ l dq v
    iintro %Φ ⟨Hb, %Hnn⟩ HΦ
    icases (bytesPointsto_singleton l dq v).2 $$ Hb with Hbs
    wp_apply_core wp_load_plain_scalar _ l dq [v] #v rfl
      (by rw [go.intoVal_unfold w8]; simp [bytesVal, bytesNat]) $$ Hbs
    iintro Hbs
    icases (bytesPointsto_singleton l dq v).1 $$ Hbs with Hb
    iapply HΦ
    iframe Hb
    ipureintro; assumption
  · intro s E t _ l v w
    iintro %Φ ⟨Hb, %Hnn⟩ HΦ
    icases (bytesPointsto_singleton l _ v).2 $$ Hb with Hbs
    wp_apply_core wp_store_plain_scalar _ l [v] [w] #v #w rfl
      (by rw [go.intoVal_unfold w8]; simp [bytesVal, bytesNat])
      (by rw [go.intoVal_unfold w8]; simp [valBytes, natBytes]) $$ Hbs
    iintro Hbs
    icases (bytesPointsto_singleton l _ w).1 $$ Hbs with Hb
    iapply HΦ
    iframe Hb
    ipureintro; assumption
  · infer_instance))

/-- Prove `IntoValTypedUnderlying (BitVec (8 * w)) t` for a plain scalar type `t` of `w` bytes,
whose typed points-to is `bytesTypedPointsto w`. -/
macro "solve_into_val_typed_bytes" : tactic => `(tactic| (
  constructor
  all_goals try simp only [typedPointsto_unseal, typedPointstoWrap, typedPointstoDef_w64,
    typedPointstoDef_w32, typedPointstoDef_w16]
  · intro s E t _ v
    iapply wp_alloc_plain_scalar _ #v (natBytes _ v.toNat) (by rw [go.intoVal_unfold]; rfl)
  · intro s E t _ l dq v
    iintro %Φ ⟨Hbs, %Hnn⟩ HΦ
    wp_apply_core wp_load_plain_scalar _ l dq (natBytes _ v.toNat) #v (natBytes_length _ _)
      (bytesVal_valBytes (by rw [go.intoVal_unfold]; rfl)) $$ Hbs
    iintro Hbs
    iapply HΦ
    iframe Hbs
    ipureintro; assumption
  · intro s E t _ l v w
    iintro %Φ ⟨Hbs, %Hnn⟩ HΦ
    wp_apply_core wp_store_plain_scalar _ l (natBytes _ v.toNat) (natBytes _ w.toNat) #v #w
      (natBytes_length _ _) (bytesVal_valBytes (by rw [go.intoVal_unfold]; rfl))
      (by rw [go.intoVal_unfold]; rfl) $$ Hbs
    iintro Hbs
    iapply HΦ
    iframe Hbs
    ipureintro; assumption
  · infer_instance))

instance intoVal_typed_uint64 : IntoValTypedUnderlying (GF := GF) w64 go.uint64 := by
  solve_into_val_typed_bytes
instance intoVal_typed_uint32 : IntoValTypedUnderlying (GF := GF) w32 go.uint32 := by
  solve_into_val_typed_bytes
instance intoVal_typed_uint16 : IntoValTypedUnderlying (GF := GF) w16 go.uint16 := by
  solve_into_val_typed_bytes
instance intoVal_typed_uint8 : IntoValTypedUnderlying (GF := GF) w8 go.uint8 := by
  solve_into_val_typed_byte
instance intoVal_typed_uint : IntoValTypedUnderlying (GF := GF) w64 go.uint := by
  solve_into_val_typed_bytes
/-- See `go.UintptrSemantics`. -/
instance intoVal_typed_uintptr : IntoValTypedUnderlying (GF := GF) w64 go.uintptr := by
  solve_into_val_typed_bytes
instance intoVal_typed_int64 : IntoValTypedUnderlying (GF := GF) w64 go.int64 := by
  solve_into_val_typed_bytes
instance intoVal_typed_int32 : IntoValTypedUnderlying (GF := GF) w32 go.int32 := by
  solve_into_val_typed_bytes
instance intoVal_typed_int16 : IntoValTypedUnderlying (GF := GF) w16 go.int16 := by
  solve_into_val_typed_bytes
instance intoVal_typed_int8 : IntoValTypedUnderlying (GF := GF) w8 go.int8 := by
  solve_into_val_typed_byte
instance intoVal_typed_int : IntoValTypedUnderlying (GF := GF) w64 go.int := by
  solve_into_val_typed_bytes
instance intoVal_typed_bool : IntoValTypedUnderlying (GF := GF) Bool go.bool := by
  solve_into_val_typed
instance intoVal_typed_string : IntoValTypedUnderlying (GF := GF) GoString go.string := by
  solve_into_val_typed
instance intoVal_typed_Pointer : IntoValTypedUnderlying (GF := GF) Loc unsafe.Pointer := by
  solve_into_val_typed
instance intoVal_typed_proph_id :
    IntoValTypedUnderlying (GF := GF) Perennial.proph_id go.prophId := by
  solve_into_val_typed
instance intoVal_typed_float64 : IntoValTypedUnderlying (GF := GF) w64 go.float64 := by
  solve_into_val_typed_bytes
instance intoVal_typed_float32 : IntoValTypedUnderlying (GF := GF) w32 go.float32 := by
  solve_into_val_typed_bytes

end into_val_typed_instances

end Perennial
