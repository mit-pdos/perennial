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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

attribute [local instance] go.tagged_internal_inst

/-- The cells of `rawCells` hold bytes: some `n` of them. -/
theorem rawCells_bytes (l : Loc) (n : Nat) :
    rawCells l (n : Int) ⊢
      (∃ bs : List w8, ⌜bs.length = n⌝ ∗ pointstoVals l (DFrac.own 1) (byteVals bs) : IProp GF) := by
  unfold rawCells pointstoVals byteVals
  rw [show ((n : Int)).toNat = n by omega]
  induction n generalizing l with
  | zero =>
    iintro _; iexists []; isplit
    · ipureintro; rfl
    · simp only [List.map_nil]; iapply BigSepL.bigSepL_nil.2; itrivial
  | succ n ih =>
    rw [List.range_succ_eq_map]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%b, H0⟩, H⟩
    rw [BigSepL.bigSepL_map]
    have Hk : ∀ k : Nat, l +ₗ (((k + 1 : Nat) : Nat) : Int) = (l +ₗ 1) +ₗ ((k : Nat) : Int) := by
      intro k; rw [loc_add_assoc]; congr 1; omega
    simp only [Hk]
    icases ih (l +ₗ 1) $$ H with ⟨%bs, %hlen, H⟩
    iexists b :: bs
    isplit
    · ipureintro; simp [hlen]
    · simp only [List.map_cons]
      iapply BigSepL.bigSepL_cons.2
      simp only [Int.natCast_zero, loc_add_0]
      iframe H0
      have Hk' : ∀ k : Nat, l +ₗ ((k + 1 : Nat) : Int) = (l +ₗ 1) +ₗ (k : Int) := by
        intro k; rw [loc_add_assoc]; congr 1; omega
      simp only [Hk']
      iexact H

/-- A store of a word into raw cells (bytes) through a type `t` of underlying word type `u`. -/
theorem word_wp_store_raw (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V] (u : go.GoType)
    (n : Nat) [hw : go.IsWordType u n] (toZ : V → Int) (hn : 0 < n)
    (hdef : ∀ l (v : V) dq,
      TypedPointsto.typedPointstoDef (GF := GF) (V := V) l v dq =
        pointstoVals l dq (byteVals (leBytes n (toZ v))))
    (hz : ∀ v : V, wordLitZ? n #v = some (toZ v))
    {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u u] (l : Loc) (w : V) :
    {{ (⌜l.locCar ≠ 0⌝ ∗ rawCells l (n : Int) : IProp GF) }}
      (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w))) @ s; E
    {{ RET #(); l ↦ w }} := by
  iintro %Φ ⟨%Hc, Hraw⟩ HΦ
  icases rawCells_bytes l n $$ Hraw with ⟨%bs, %hlen, Hl⟩
  wp_pures
  have hev : wordOpEval n .swap (leInt bs) #w = some (wordLit n (leInt bs), some (toZ w)) := by
    simp [wordOpEval, hz]
  wp_apply_core wp_atomic_word_write n .swap l bs #w _ (toZ w) hn hlen hev $$ [Hl]
  · iexact Hl
  iintro Hl
  wp_pures
  iapply HΦ
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  simp only [hdef]
  iframe Hl
  ipureintro; intro h; subst h; exact Hc rfl

/-- `IntoValTypedUnderlying V u` for a word type `u` of `n` bytes (`IsWordType`), whose typed
points-to is its little-endian bytes (`wordTypedPointsto`). -/
theorem word_into_val_typed (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V] (u : go.GoType)
    (n : Nat) [hw : go.IsWordType u n] (hrepr : go.TypeReprUnderlying u V) (toZ : V → Int)
    (hn : 0 < n ∧ n < 2^62)
    (hsize : typeSize V = n)
    (hdef : ∀ l (v : V) dq,
      TypedPointsto.typedPointstoDef (GF := GF) (V := V) l v dq =
        pointstoVals l dq (byteVals (leBytes n (toZ v))))
    (hlit : ∀ v : V, (#v : val) = wordLit n (toZ v % 2 ^ (8 * n)))
    (hz : ∀ v : V, wordLitZ? n #v = some (toZ v))
    (hunder : u ↓u u) :
    IntoValTypedUnderlying (GF := GF) V u where
  wp_alloc_def {s E t} _ v := by
    iintro %Φ _ HΦ
    wp_pures
    iapply (wp_alloc_raw u n ⟨by omega, by omega⟩ #v (fun l => typedPointsto l v (DFrac.own 1))
      (fun l => word_wp_store_raw V u n toZ hn.1 hdef hz (t := u) l v))
    · itrivial
    · inext; iexact HΦ
  wp_load_def {s E t} _ l dq v := by
    iintro %Φ Hl HΦ
    rw [typedPointsto_unseal]; unfold typedPointstoWrap
    icases Hl with ⟨Hl, %Hnn⟩
    simp only [hdef]
    wp_pures
    have hev : wordOpEval n .load (leInt (leBytes n (toZ v))) #() = some (#v, none) := by
      simp only [wordOpEval, leInt_leBytes, hlit]
    wp_apply_core wp_atomic_word_read n .load l dq (leBytes n (toZ v)) #() #v hn.1
      (leBytes_length n _) hev $$ [Hl]
    · iexact Hl
    iintro Hl
    iapply HΦ
    iframe Hl
    ipureintro; exact Hnn
  wp_store_def {s E t} _ l v w := by
    iintro %Φ Hl HΦ
    rw [typedPointsto_unseal]; unfold typedPointstoWrap
    icases Hl with ⟨Hl, %Hnn⟩
    simp only [hdef]
    wp_pures
    have hev : wordOpEval n .swap (leInt (leBytes n (toZ v))) #w = some (#v, some (toZ w)) := by
      show (wordLitZ? n #w).map (fun z => (wordLit n (leInt (leBytes n (toZ v))), some z)) = _
      rw [hz, leInt_leBytes, ← hlit]
      rfl
    wp_apply_core wp_atomic_word_write n .swap l (leBytes n (toZ v)) #w #v (toZ w) hn.1
      (leBytes_length n _) hev $$ [Hl]
    · iexact Hl
    iintro Hl
    wp_pures
    iapply HΦ
    iframe Hl
    ipureintro; exact Hnn
  wp_store_raw_def {s E t} _ l w := by
    rw [hsize]
    exact word_wp_store_raw V u n toZ hn.1 hdef hz l w
  type_repr_def := hrepr

theorem ofInt_toNat_emod {m : Nat} (x : BitVec m) : BitVec.ofInt m ((x.toNat : Int) % 2 ^ m) = x := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have e : (x.toNat : Int) % 2 ^ m = x.toNat := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hx)
  rw [e, BitVec.toNat_ofInt]
  have : ((x.toNat : Int) % (2 ^ m : Nat)) = x.toNat := by
    rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast hx)]
  rw [this]; simp

/-- A `w64` type's instance (`uint64`, `int64`, `uint`, `int`, `uintptr`, `float64`). -/
macro "solve_into_val_typed_w64" : tactic => `(tactic|
  exact word_into_val_typed w64 _ 8 (by infer_instance) (fun x => x.toNat) ⟨by decide, by decide⟩ go.typeSize_w64
    (fun _ _ _ => rfl) (fun v => by
      rw [go.intoVal_unfold w64]
      show LitV (LitInt v) = LitV (LitInt (BitVec.ofInt 64 ((v.toNat : Int) % 2 ^ 64)))
      rw [ofInt_toNat_emod])
    (fun v => by rw [go.intoVal_unfold w64]; rfl) inferInstance)
macro "solve_into_val_typed_w32" : tactic => `(tactic|
  exact word_into_val_typed w32 _ 4 (by infer_instance) (fun x => x.toNat) ⟨by decide, by decide⟩ go.typeSize_w32
    (fun _ _ _ => rfl) (fun v => by
      rw [go.intoVal_unfold w32]
      show LitV (LitInt32 v) = LitV (LitInt32 (BitVec.ofInt 32 ((v.toNat : Int) % 2 ^ 32)))
      rw [ofInt_toNat_emod])
    (fun v => by rw [go.intoVal_unfold w32]; rfl) inferInstance)
macro "solve_into_val_typed_w16" : tactic => `(tactic|
  exact word_into_val_typed w16 _ 2 (by infer_instance) (fun x => x.toNat) ⟨by decide, by decide⟩ go.typeSize_w16
    (fun _ _ _ => rfl) (fun v => by
      rw [go.intoVal_unfold w16]
      show LitV (LitInt16 v) = LitV (LitInt16 (BitVec.ofInt 16 ((v.toNat : Int) % 2 ^ 16)))
      rw [ofInt_toNat_emod])
    (fun v => by rw [go.intoVal_unfold w16]; rfl) inferInstance)

/-- A type whose values are `n`-byte words (`toZ`): what the atomic operations on its typed
points-to need. -/
class WordRepr (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V] (n : outParam Nat) where
  toZ : V → Int
  hn : 0 < n
  range : ∀ v, 0 ≤ toZ v ∧ toZ v < 2 ^ (8 * n)
  hdef : ∀ l (v : V) dq,
    TypedPointsto.typedPointstoDef (GF := GF) (V := V) l v dq =
      pointstoVals l dq (byteVals (leBytes n (toZ v)))
  hlit : ∀ v : V, (#v : val) = wordLit n (toZ v)
  hlitmod : ∀ z, wordLit n z = wordLit n (z % 2 ^ (8 * n))
  hz : ∀ v : V, wordLitZ? n #v = some (toZ v)
  hinj : ∀ v w : V, toZ v = toZ w → v = w

theorem wordLit_w64 (z : Int) : wordLit 8 z = wordLit 8 (z % 2 ^ (8 * 8)) := by
  show LitV (LitInt (BitVec.ofInt 64 z)) = LitV (LitInt (BitVec.ofInt 64 (z % 2 ^ 64)))
  congr 2; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]
theorem wordLit_w32 (z : Int) : wordLit 4 z = wordLit 4 (z % 2 ^ (8 * 4)) := by
  show LitV (LitInt32 (BitVec.ofInt 32 z)) = LitV (LitInt32 (BitVec.ofInt 32 (z % 2 ^ 32)))
  congr 2; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]
theorem wordLit_w16 (z : Int) : wordLit 2 z = wordLit 2 (z % 2 ^ (8 * 2)) := by
  show LitV (LitInt16 (BitVec.ofInt 16 z)) = LitV (LitInt16 (BitVec.ofInt 16 (z % 2 ^ 16)))
  congr 2; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]

instance wordRepr_w64 : WordRepr (GF := GF) w64 8 where
  toZ x := x.toNat
  hn := by decide
  range v := ⟨by omega, by have := v.isLt; exact_mod_cast this⟩
  hdef _ _ _ := rfl
  hlit v := by
    rw [go.intoVal_unfold w64]
    show LitV (LitInt v) = LitV (LitInt (BitVec.ofInt 64 (v.toNat : Int)))
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  hlitmod := wordLit_w64
  hz v := by rw [go.intoVal_unfold w64]; rfl
  hinj v w h := BitVec.eq_of_toNat_eq (by exact_mod_cast h)
instance wordRepr_w32 : WordRepr (GF := GF) w32 4 where
  toZ x := x.toNat
  hn := by decide
  range v := ⟨by omega, by have := v.isLt; exact_mod_cast this⟩
  hdef _ _ _ := rfl
  hlit v := by
    rw [go.intoVal_unfold w32]
    show LitV (LitInt32 v) = LitV (LitInt32 (BitVec.ofInt 32 (v.toNat : Int)))
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  hlitmod := wordLit_w32
  hz v := by rw [go.intoVal_unfold w32]; rfl
  hinj v w h := BitVec.eq_of_toNat_eq (by exact_mod_cast h)
instance wordRepr_w16 : WordRepr (GF := GF) w16 2 where
  toZ x := x.toNat
  hn := by decide
  range v := ⟨by omega, by have := v.isLt; exact_mod_cast this⟩
  hdef _ _ _ := rfl
  hlit v := by
    rw [go.intoVal_unfold w16]
    show LitV (LitInt16 v) = LitV (LitInt16 (BitVec.ofInt 16 (v.toNat : Int)))
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  hlitmod := wordLit_w16
  hz v := by rw [go.intoVal_unfold w16]; rfl
  hinj v w h := BitVec.eq_of_toNat_eq (by exact_mod_cast h)

theorem toZ_add_w64 (a b : w64) :
    (wordRepr_w64 (GF := GF)).toZ (a + b) =
      ((wordRepr_w64 (GF := GF)).toZ a + (wordRepr_w64 (GF := GF)).toZ b) % 2 ^ (8 * 8) := by
  show ((a + b).toNat : Int) = ((a.toNat : Int) + b.toNat) % 2 ^ 64
  rw [BitVec.toNat_add]; omega
theorem toZ_add_w32 (a b : w32) :
    (wordRepr_w32 (GF := GF)).toZ (a + b) =
      ((wordRepr_w32 (GF := GF)).toZ a + (wordRepr_w32 (GF := GF)).toZ b) % 2 ^ (8 * 4) := by
  show ((a + b).toNat : Int) = ((a.toNat : Int) + b.toNat) % 2 ^ 32
  rw [BitVec.toNat_add]; omega

section word_atomics
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {n : Nat} [W : WordRepr (GF := GF) V n]
variable {s : Stuckness} {E : CoPset}

theorem WordRepr.leInt_bytes (v : V) : leInt (leBytes n (W.toZ v)) = W.toZ v := by
  rw [leInt_leBytes]
  exact Int.emod_eq_of_lt (W.range v).1 (W.range v).2

theorem wp_word_load (l : Loc) (dq : DFrac) (v : V) :
    {{ ▷ (l ↦{dq} v : IProp GF) }} (AtomicWord n .load (Val #l) (Val #())) @ s; E
    {{ RET #v; l ↦{dq} v }} := by
  iintro %Φ Hl HΦ
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  icases Hl with ⟨Hl, >%Hnn⟩
  simp only [W.hdef]
  iapply (wp_atomic_word_read n .load l dq (leBytes n (W.toZ v)) #() #v W.hn (leBytes_length n _)
    (by simp only [wordOpEval, W.leInt_bytes, W.hlit])) $$ Hl
  inext; iintro Hl
  iapply HΦ; iframe Hl; ipureintro; exact Hnn

theorem wp_word_swap (l : Loc) (v v' : V) :
    {{ ▷ (l ↦ v : IProp GF) }} (AtomicWord n .swap (Val #l) (Val #v')) @ s; E
    {{ RET #v; l ↦ v' }} := by
  iintro %Φ Hl HΦ
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  icases Hl with ⟨Hl, >%Hnn⟩
  simp only [W.hdef]
  iapply (wp_atomic_word_write n .swap l (leBytes n (W.toZ v)) #v' #v (W.toZ v') W.hn
    (leBytes_length n _) (by
      show (wordLitZ? n #v').map (fun z => (wordLit n (leInt (leBytes n (W.toZ v))), some z)) = _
      rw [W.hz, W.leInt_bytes, ← W.hlit]; rfl)) $$ Hl
  inext; iintro Hl
  iapply HΦ; iframe Hl; ipureintro; exact Hnn

/-- `add`: the sum, wrapping (`r` its word). -/
theorem wp_word_add (l : Loc) (v d r : V) (hr : W.toZ r = (W.toZ v + W.toZ d) % 2 ^ (8 * n)) :
    {{ ▷ (l ↦ v : IProp GF) }} (AtomicWord n .add (Val #l) (Val #d)) @ s; E
    {{ RET #r; l ↦ r }} := by
  iintro %Φ Hl HΦ
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  icases Hl with ⟨Hl, >%Hnn⟩
  simp only [W.hdef]
  iapply (wp_atomic_word_write n .add l (leBytes n (W.toZ v)) #d #r (W.toZ v + W.toZ d) W.hn
    (leBytes_length n _) (by
      show (wordLitZ? n #d).map (fun z => (wordLit n (leInt (leBytes n (W.toZ v)) + z),
        some (leInt (leBytes n (W.toZ v)) + z))) = _
      rw [W.hz, W.leInt_bytes, W.hlit r, hr, ← W.hlitmod]; rfl)) $$ Hl
  inext; iintro Hl
  iapply HΦ
  rw [hr, leBytes_emod]
  iframe Hl; ipureintro; exact Hnn

theorem wp_word_cmpxchg_suc (l : Loc) (v v1 v2 : V) (h : v = v1) :
    {{ ▷ (l ↦ v : IProp GF) }} (AtomicWord n .cmpxchg (Val #l) (Val (PairV #v1 #v2))) @ s; E
    {{ RET (PairV #v #true); l ↦ v2 }} := by
  subst h
  iintro %Φ Hl HΦ
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  icases Hl with ⟨Hl, >%Hnn⟩
  simp only [W.hdef]
  iapply (wp_atomic_word_write n .cmpxchg l (leBytes n (W.toZ v)) (PairV #v #v2) (PairV #v #true)
    (W.toZ v2) W.hn (leBytes_length n _) (by
      simp only [wordOpEval, W.hz, W.leInt_bytes, ↓reduceIte, ← W.hlit]
      rw [go.intoVal_unfold Bool])) $$ Hl
  inext; iintro Hl
  iapply HΦ; iframe Hl; ipureintro; exact Hnn

theorem wp_word_cmpxchg_fail (l : Loc) (dq : DFrac) (v v1 v2 : V) (h : v ≠ v1) :
    {{ ▷ (l ↦{dq} v : IProp GF) }} (AtomicWord n .cmpxchg (Val #l) (Val (PairV #v1 #v2))) @ s; E
    {{ RET (PairV #v #false); l ↦{dq} v }} := by
  iintro %Φ Hl HΦ
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  icases Hl with ⟨Hl, >%Hnn⟩
  simp only [W.hdef]
  have hne : W.toZ v ≠ W.toZ v1 := fun e => h (W.hinj _ _ e)
  iapply (wp_atomic_word_read n .cmpxchg l dq (leBytes n (W.toZ v)) (PairV #v1 #v2)
    (PairV #v #false) W.hn (leBytes_length n _) (by
      simp only [wordOpEval, W.hz, W.leInt_bytes, hne, ↓reduceIte, ← W.hlit]
      rw [go.intoVal_unfold Bool])) $$ Hl
  inext; iintro Hl
  iapply HΦ; iframe Hl; ipureintro; exact Hnn

include W in
/-- A word's full points-to and a discarded one are not at the same place. -/
theorem word_pointsto_own_discard (l : Loc) (v w : V) :
    (l ↦ v ∗ l ↦□ w : IProp GF) ⊢ False := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  simp only [W.hdef]
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  have hn := W.hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold pointstoVals byteVals
  simp only [leBytes, List.map_cons]
  icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨H1, -⟩
  icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨H2, -⟩
  icombine H1 H2 gives %H
  exact absurd (DFrac.valid_own_op_discard.1 H.1) (by simp)

include W in
/-- Two full points-tos of a word are not at the same place. -/
theorem word_pointsto_excl (l : Loc) (v w : V) :
    (l ↦ v ∗ l ↦ w : IProp GF) ⊢ False := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  simp only [W.hdef]
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  have hn := W.hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold pointstoVals byteVals
  simp only [leBytes, List.map_cons]
  icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨H1, -⟩
  icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨H2, -⟩
  icombine H1 H2 gives %H
  exact absurd (DFrac.valid_op_own H.1) (by simp)

end word_atomics

instance intoVal_typed_uint64 : IntoValTypedUnderlying (GF := GF) w64 go.uint64 := by
  solve_into_val_typed_w64
instance intoVal_typed_uint32 : IntoValTypedUnderlying (GF := GF) w32 go.uint32 := by
  solve_into_val_typed_w32
instance intoVal_typed_uint16 : IntoValTypedUnderlying (GF := GF) w16 go.uint16 := by
  solve_into_val_typed_w16
instance intoVal_typed_uint8 : IntoValTypedUnderlying (GF := GF) w8 go.uint8 := by
  solve_into_val_typed
instance intoVal_typed_uint : IntoValTypedUnderlying (GF := GF) w64 go.uint := by
  solve_into_val_typed_w64
/-- See `go.UintptrSemantics`. -/
instance intoVal_typed_uintptr : IntoValTypedUnderlying (GF := GF) w64 go.uintptr := by
  solve_into_val_typed_w64
instance intoVal_typed_int64 : IntoValTypedUnderlying (GF := GF) w64 go.int64 := by
  solve_into_val_typed_w64
instance intoVal_typed_int32 : IntoValTypedUnderlying (GF := GF) w32 go.int32 := by
  solve_into_val_typed_w32
instance intoVal_typed_int16 : IntoValTypedUnderlying (GF := GF) w16 go.int16 := by
  solve_into_val_typed_w16
instance intoVal_typed_int8 : IntoValTypedUnderlying (GF := GF) w8 go.int8 := by
  solve_into_val_typed
instance intoVal_typed_int : IntoValTypedUnderlying (GF := GF) w64 go.int := by
  solve_into_val_typed_w64
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
  solve_into_val_typed_w64
instance intoVal_typed_float32 : IntoValTypedUnderlying (GF := GF) w32 go.float32 := by
  solve_into_val_typed_w32

end into_val_typed_instances

end Perennial
