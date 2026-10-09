/-
Specs for `math/big`: `NewInt` and `(*Int).Int64`.

`ownInt p z` owns the `big.Int` at `p` and says it holds `z`. An `Int` is a sign
`neg` and a magnitude `abs`, a little-endian slice of 64-bit words. The
magnitude need not be normalized (Go keeps it normalized, but nothing here needs
that), so a value has several representations.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.math.big
public import Perennial.GeneratedProof.math.big

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace math.big

/-- The value of a little-endian list of 64-bit words. -/
def natValue : List w64 → Int
  | [] => 0
  | w :: ws => uint.Z w + 2 ^ 64 * natValue ws

theorem natValue_nonneg : ∀ ws : List w64, 0 ≤ natValue ws
  | [] => by unfold natValue; omega
  | w :: ws => by
    have := natValue_nonneg ws
    unfold natValue; have : 0 ≤ uint.Z w := by word
    omega

/-- A magnitude below `2^64` is its low word. -/
theorem natValue_small (ws : List w64) (h : natValue ws < 2 ^ 64) :
    natValue ws = uint.Z (ws.headD (W64 0)) := by
  cases ws with
  | nil => simp [natValue]; rfl
  | cons w ws =>
    have := natValue_nonneg ws
    have : 0 ≤ uint.Z w := by word
    simp only [natValue, List.headD] at h ⊢
    have : natValue ws = 0 := by omega
    omega

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.big.Assumptions]

/-- `ownInt p z`: the `big.Int` at `p` holds `z`. Exclusive, since a `big.Int`
is mutable. -/
def ownInt (p : Loc) (z : Int) : IProp GF :=
  iprop(∃ (x : Int') (ws : List w64),
    p ↦ x ∗ x.abs' ↦* ws ∗
    ⌜z = if x.neg' then - natValue ws else natValue ws⌝)

theorem wp_NewInt (v : w64) :
    {{ (True : IProp GF) }}
      (App (Val (@! NewInt)) (Val #v))
    {{ (p : Loc), RET #p; ownInt p (sint.Z v) }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · wp_if_destruct
    · exfalso; revert ‹sint.Z (W64 0) < _›; decide
    wp_apply wp_slice_literal (V := w64) [-v]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_alloc p as Hp
    wp_auto
    iapply HΦ
    unfold ownInt
    iexists _, [-v]
    iframe
    ipureintro
    simp only [decide_eq_true ‹sint.Z v < sint.Z (W64 0)›, ↓reduceIte, natValue]
    word
  · wp_if_destruct
    · wp_alloc p as Hp
      wp_auto
      iapply HΦ
      unfold ownInt
      iexists _, []
      iframe
      isplitl
      · iapply ownSlice_nil
      ipureintro
      simp [natValue]
    wp_apply wp_slice_literal (V := w64) [v]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_alloc p as Hp
    wp_auto
    iapply HΦ
    unfold ownInt
    iexists _, [v]
    iframe
    ipureintro
    simp only [decide_eq_false ‹¬sint.Z v < sint.Z (W64 0)›, Bool.false_eq_true, ↓reduceIte, natValue]
    word

theorem wp_low64 (s : GoSlice) (ws : List w64) (dq : DFrac) :
    {{ (s ↦*{dq} ws : IProp GF) }}
      (App (Val (@! low64)) (Val #s))
    {{ RET #(ws.headD (W64 0)); s ↦*{dq} ws }} := by
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_if_destruct
  · have : ws = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hlen.1, Hif]; rfl
    subst this
    simp only [List.headD]
    iapply HΦ $$ Hs
  obtain ⟨w, ws', rfl⟩ : ∃ w ws', ws = w :: ws' := by
    cases ws with
    | nil => exfalso; apply Hif; simp at Hlen; word
    | cons w ws' => exact ⟨w, ws', rfl⟩
  simp only [List.length_cons] at Hlen
  have Hpos : 0 < sint.Z s.len := by
    have := Hlen.1
    have : (sint.nat s.len : Int) = sint.Z s.len := by word
    omega
  have H0 : sint.Z (W64 0) = 0 := rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) (w :: ws') dq w (by omega) $$ [Hs] with Hs
  · iframe Hs; ipureintro; rfl
  simp only [List.headD]
  iapply HΦ $$ Hs

theorem wp_Int64 (p : Loc) (z : Int) (Hz : - 2 ^ 63 ≤ z ∧ z < 2 ^ 63) :
    {{ ownInt (GF := GF) p z }}
      (App (Val (p @!! go.GoType.PointerType Int'.ty @!! go!"Int64")) (Val #()))
    {{ RET #(W64 z); ownInt p z }} := by
  wp_start as H
  unfold ownInt
  icases H with ⟨%x, %ws, Hp, Hws, %Hz⟩
  wp_auto
  wp_apply wp_low64 $$ [Hws] with Hws
  · iexact Hws
  have Hsmall := natValue_small ws (by split at Hz <;> omega)
  generalize ws.headD (W64 0) = w at Hsmall
  wp_auto
  cases Hneg : x.neg'
  all_goals
    simp only [Hneg, Bool.false_eq_true, ↓reduceIte] at Hz ⊢
    wp_auto
  · rw [show w = W64 z by rw [Hz, Hsmall]; word]
    iapply HΦ
    iexists x, ws
    iframe
    ipureintro
    simp only [Hneg, Bool.false_eq_true, ↓reduceIte, Hz]
  · rw [show -w = W64 z by rw [Hz, Hsmall]; word]
    iapply HΦ
    iexists x, ws
    iframe
    ipureintro
    simp only [Hneg, ↓reduceIte, Hz]

end wps

end math.big

end Perennial
end
