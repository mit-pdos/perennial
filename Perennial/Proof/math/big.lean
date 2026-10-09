/-
Specs for `math/big`: `NewInt` and `(*Int).Int64`.

`ownInt p z` owns the `big.Int` at `p` and says it holds `z`. An `Int` is a sign
`neg` and a magnitude `abs`, a little-endian slice of 64-bit words. The
magnitude is normalized, as Go keeps it: no most significant zero word
(`natNormalized`), so a value has one representation (`crypto/rand.Int`'s model relies
on it: `0 < z < 2^63` is a one-word magnitude).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.math.big
public import Perennial.GeneratedProof.math.big
public import Perennial.Proof.fmt

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

/-- No most significant zero word: how Go keeps a magnitude (`nat.norm`). -/
def natNormalized (ws : List w64) : Prop := ws.getLast? ≠ some (W64 0)

/-- A normalized magnitude with a word is positive. -/
theorem natValue_pos : ∀ ws : List w64, ws ≠ [] → natNormalized ws → 0 < natValue ws
  | [], h, _ => absurd rfl h
  | [w], _, hn => by
    simp only [natNormalized, List.getLast?_singleton, ne_eq, Option.some.injEq] at hn
    have : uint.Z w ≠ 0 := fun h => hn (by word)
    have : 0 ≤ uint.Z w := by word
    simp only [natValue]; omega
  | w :: w' :: ws, _, hn => by
    have ih := natValue_pos (w' :: ws) (List.cons_ne_nil _ _)
      (by simpa [natNormalized, List.getLast?_cons_cons] using hn)
    have : 0 ≤ uint.Z w := by word
    simp only [natValue] at ih ⊢; omega

/-- A normalized magnitude below `2^64` with a word is that one word. -/
theorem natValue_one_word (ws : List w64) (hne : ws ≠ []) (hn : natNormalized ws)
    (h : natValue ws < 2 ^ 64) : ∃ w, ws = [w] := by
  rcases ws with _ | ⟨w, _ | ⟨w', ws⟩⟩
  · exact absurd rfl hne
  · exact ⟨w, rfl⟩
  · have hpos := natValue_pos (w' :: ws) (List.cons_ne_nil _ _)
      (by simpa [natNormalized, List.getLast?_cons_cons] using hn)
    have : 0 ≤ uint.Z w := by word
    simp only [natValue] at h hpos; omega

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.math.big :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math.big :=
  build_get_is_pkg_init_wf

variable [package_sem : math.big.Assumptions]

/-- `ownInt p z`: the `big.Int` at `p` holds `z`. Exclusive, since a `big.Int`
is mutable. -/
def ownInt (p : Loc) (z : Int) : IProp GF :=
  iprop(∃ (x : Int') (ws : List w64),
    p ↦ x ∗ x.abs' ↦* ws ∗
    ⌜(z = if x.neg' then - natValue ws else natValue ws) ∧ natNormalized ws⌝)

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
    refine ⟨?_, ?_⟩
    · simp only [decide_eq_true ‹sint.Z v < sint.Z (W64 0)›, ↓reduceIte, natValue]
      word
    · simp only [natNormalized, List.getLast?_singleton, ne_eq, Option.some.injEq]
      intro h
      have : sint.Z v < 0 := ‹sint.Z v < sint.Z (W64 0)›
      have : v = W64 0 := by rw [show v = - -v by simp, h]; rfl
      subst this; simp at *
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
      simp [natValue, natNormalized]
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
    refine ⟨?_, ?_⟩
    · simp only [decide_eq_false ‹¬sint.Z v < sint.Z (W64 0)›, Bool.false_eq_true, ↓reduceIte,
        natValue]
      word
    · simp only [natNormalized, List.getLast?_singleton, ne_eq, Option.some.injEq]
      exact ‹¬v = W64 0›

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
  icases H with ⟨%x, %ws, Hp, Hws, %Hz, %Hnorm⟩
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
    exact ⟨by simp only [Hneg, Bool.false_eq_true, ↓reduceIte, Hz], Hnorm⟩
  · rw [show -w = W64 z by rw [Hz, Hsmall]; word]
    iapply HΦ
    iexists x, ws
    iframe
    ipureintro
    exact ⟨by simp only [Hneg, ↓reduceIte, Hz], Hnorm⟩

end wps

end math.big

end Perennial
end
