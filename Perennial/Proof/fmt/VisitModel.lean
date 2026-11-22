/-
Specs of the helpers of the model of `fmt` (`Perennial/TrustedCode/fmt.lean`) that call the
arguments' formatting methods (`visitRest`, `visitArg`) and decide which arguments the model
formats exactly (`inert`), with the directive parser (`parseDirective`); none is a function of
package `fmt`.
-/
module

public import Perennial.Proof.fmt.Args
public import Perennial.Proof.fmt.SprintfModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace fmt

section defs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The signature of `fmt.Formatter`'s `Format(State, rune)`. -/
def formatSig : go.signature := go.Signature [go.Named go!"fmt.State" [], go.rune] false []

/-- The type implements one of the interfaces Go's `handleMethods` consults: `Formatter`,
`GoStringer`, `error`, `Stringer` (by signature, as Go's type switch does). -/
def HasFmtSig (t : go.GoType) : Prop :=
  methodSet t !! go!"Format" = some formatSig ∨ methodSet t !! go!"GoString" = some noArgStringSig ∨
  methodSet t !! go!"Error" = some noArgStringSig ∨ methodSet t !! go!"String" = some noArgStringSig

/-- The values Go formats under any directive calling none of their methods and reading no memory,
as the model's `inert` tells them: the predeclared basic types, and the types of integer or string
kind implementing none of `handleMethods`' interfaces. -/
def InertTy (t : go.GoType) : Prop :=
  IsBasicType t ∨ (¬ HasFmtSig t ∧ (underlying t = go.string ∨ IsIntType (underlying t)))

/-- The phase of the directive parser `parseDirective`'s variables `phase` and `n`. -/
def dirPh (phase n : w64) : DirPhase :=
  if sint.Z phase = 0 then .flags else if sint.Z phase = 1 then .width (sint.nat n)
  else .prec (sint.nat n)

/-- The directives after reading the verb `c` of a directive (`%%` consumes no argument). -/
def dirCons (c : w8) (sharpV : Bool) (r : Option (List Directive)) : Option (List Directive) :=
  if c = W8 37 then r else (⟨c, sharpV⟩ :: ·) <$> r

theorem dirPh_zero (n : w64) : dirPh (W64 0) n = .flags := rfl
theorem dirPh_one (n : w64) : dirPh (W64 1) n = .width (sint.nat n) := rfl
theorem dirPh_two (n : w64) : dirPh (W64 2) n = .prec (sint.nat n) := rfl
theorem sint_Z_W64_byte (c : w8) : sint.Z (W64 (uint.Z c)) = uint.Z c := by word
theorem W8_uint_Z (c : w8) : W8 (uint.Z c) = c := by word
theorem sint_nat_W64_one : sint.nat (W64 1) = 1 := rfl
theorem sint_nat_W64_zero : sint.nat (W64 0) = 0 := rfl
theorem nat_lt_eq_false_of_le {a b : Nat} (h : b ≤ a) : (a < b) = False := by
  simp only [eq_iff_iff, iff_false, Nat.not_lt]; exact h
theorem nat_le_eq_false_of_lt {a b : Nat} (h : b < a) : (a ≤ b) = False := by
  simp only [eq_iff_iff, iff_false, Nat.not_le]; exact h

theorem uint_Z_byte_bounds (c : w8) : 0 ≤ uint.Z c ∧ uint.Z c < 256 := ⟨by word, by word⟩

theorem phase_cases (ph : w64) (h : sint.Z ph = 0 ∨ sint.Z ph = 1 ∨ sint.Z ph = 2) :
    ph = W64 0 ∨ ph = W64 1 ∨ ph = W64 2 := by
  rcases h with h | h | h
  · left; word
  · right; left; word
  · right; right; word

/-- The arithmetic of a step of `parseDirective`'s loop. -/
theorem parseDirective_arith (format : GoString) (i iv : w64)
    (Hi : 0 ≤ sint.Z i ∧ sint.Z i ≤ (format.length : Int)) (Hlen : (format.length : Int) < 2 ^ 63)
    (Hiv : sint.Z i ≤ sint.Z iv ∧ sint.Z iv ≤ (format.length : Int))
    (Hlt : sint.nat iv < format.length) :
    sint.nat (iv + W64 1) = sint.nat iv + 1 ∧ sint.Z i ≤ sint.Z (iv + W64 1) ∧
    sint.Z (iv + W64 1) ≤ (format.length : Int) ∧ sint.Z i < sint.Z (iv + W64 1) ∧
    (sint.Z (iv + W64 1) < sint.Z (W64 format.length) → format.drop (sint.nat iv + 1) ≠ []) ∧
    (sint.Z (W64 format.length) ≤ sint.Z (iv + W64 1) → format.length ≤ sint.nat iv + 1) := by
  have hA : sint.nat (iv + W64 1) = sint.nat iv + 1 := by word
  refine ⟨hA, by word, by word, by word, fun h => ?_, fun h => by word⟩
  apply List.ne_nil_of_length_pos
  simp only [List.length_drop]
  word

/-- The arithmetic of a digit of `parseDirective`'s width or precision. -/
theorem parseDirective_digits (nv : w64) (hn0 : 0 ≤ sint.Z nv) (hn7 : sint.Z nv ≤ 7) :
    (¬ sint.Z (W64 7) ≤ sint.Z nv →
      sint.Z (nv + W64 1) ≤ 7 ∧ 0 ≤ sint.Z (nv + W64 1) ∧ sint.nat (nv + W64 1) = sint.nat nv + 1 ∧
        sint.nat nv < maxNumDigits) ∧
    (sint.Z (W64 7) ≤ sint.Z nv → ¬ sint.nat nv < maxNumDigits) := by
  refine ⟨fun h => ⟨by word, by word, by word, ?_⟩, fun h => ?_⟩
  · unfold maxNumDigits; word
  · unfold maxNumDigits; word

theorem wrapArgsFrom_append (k n : Nat) (pre : List Directive) (d : Directive) :
    wrapArgsFrom k (pre ++ [d]) n = wrapArgsFrom k pre n ++
      (if d.verb = W8 119 ∧ k + pre.length < n then [k + pre.length] else []) := by
  induction pre generalizing k with
  | nil => simp [wrapArgsFrom]
  | cons e pre ih =>
    simp only [List.cons_append, wrapArgsFrom, ih, List.append_assoc, List.length_cons]
    rw [show k + 1 + pre.length = k + (pre.length + 1) by omega]

theorem fmtDirectivesAux_pct_drop (format : GoString) (n : Nat) (h : format[n]? = some (W8 37)) :
    fmtDirectivesAux none (format.drop n) =
      fmtDirectivesAux (some (false, .flags)) (format.drop (n + 1)) := by
  have hlt : n < format.length := by
    rcases Nat.lt_or_ge n format.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have hc : format[n] = W8 37 := by
    rw [List.getElem?_eq_getElem hlt] at h; exact Option.some.inj h
  rw [List.drop_eq_getElem_cons hlt, hc]
  exact fmtDirectivesAux_pct _

theorem w8_verb_eq (v : w64) (h0 : 0 ≤ sint.Z v) (h1 : sint.Z v < 256) (b : Nat) (hb : b < 256) :
    W8 (sint.Z v) = W8 b ↔ v = W64 b := by
  constructor
  · intro h; word
  · intro h; subst h; word

end defs

set_option hygiene false in
/-- In a proof about an argument of dynamic type `ty`: the case `ty = t` of a type assertion
`x.(t)`, closed by `close`, and the case `ty ≠ t` left, the assertion's result simplified. -/
local macro "ta_case" t:term " => " close:tactic : tactic => `(tactic| (
  by_cases hT : ty = $t
  · subst hT
    simp only [↓reduceIte, _root_.decide_true]
    wp_auto
    $close
  simp only [hT, ↓reduceIte, decide_false]
  wp_auto))

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

set_option linter.unusedSimpArgs false

set_option maxRecDepth 100000 in
/-- The helper `fmt.isBasic`: whether the argument's dynamic type is a predeclared basic type. -/
theorem wp_isBasic (x : GoInterface) :
    {{ (True : IProp GF) }}
      (App (Val isBasic) (Val #x))
    {{ (b : Bool), RET #b; ⌜b = true ↔ ∃ ii, x = interface.ok ii ∧ IsBasicType ii.ty⌝ }} := by
  iintro %Φ - HΦ
  unfold isBasic
  wp_auto
  cases x with
  | nil =>
    wp_auto
    iapply HΦ
    ipureintro
    simp
  | ok ii =>
    obtain ⟨ty, v⟩ := ii
    wp_auto
    repeat' (first | wp_if_destruct | wp_auto)
    all_goals (iapply HΦ; ipureintro)
    all_goals simp_all [IsBasicType, IsIntType]

set_option maxRecDepth 100000 in
/-- The helper `fmt.isIntKind`: whether the argument's dynamic type has one of Go's ten integer
types as its underlying type. -/
theorem wp_isIntKind (x : GoInterface) :
    {{ (True : IProp GF) }}
      (App (Val isIntKind) (Val #x))
    {{ (b : Bool), RET #b; ⌜b = true ↔ ∃ ii, x = interface.ok ii ∧ IsIntType (underlying ii.ty)⌝ }} := by
  iintro %Φ - HΦ
  unfold isIntKind kindIs
  wp_auto
  cases x with
  | nil =>
    wp_auto
    iapply HΦ
    ipureintro
    simp
  | ok ii =>
    obtain ⟨ty, v⟩ := ii
    wp_auto
    repeat' (first | wp_if_destruct | wp_auto)
    all_goals (iapply HΦ; ipureintro)
    all_goals simp_all [IsIntType]

/-- The helper `fmt.isStrKind`: whether the argument's dynamic type has `string` as its
underlying type. -/
theorem wp_isStrKind (x : GoInterface) :
    {{ (True : IProp GF) }}
      (App (Val isStrKind) (Val #x))
    {{ (b : Bool), RET #b; ⌜b = true ↔ ∃ ii, x = interface.ok ii ∧ underlying ii.ty = go.string⌝ }} := by
  iintro %Φ - HΦ
  unfold isStrKind kindIs
  wp_auto
  cases x with
  | nil =>
    iapply HΦ
    ipureintro
    simp
  | ok ii =>
    obtain ⟨ty, v⟩ := ii
    iapply HΦ
    ipureintro
    simp

/-- The helper `fmt.hasFmtMethod`: whether the argument implements one of `handleMethods`'
interfaces. -/
theorem wp_hasFmtMethod (x : GoInterface) :
    {{ (True : IProp GF) }}
      (App (Val hasFmtMethod) (Val #x))
    {{ (b : Bool), RET #b; ⌜b = true ↔ ∃ ii, x = interface.ok ii ∧ HasFmtSig ii.ty⌝ }} := by
  iintro %Φ - HΦ
  unfold hasFmtMethod
  wp_auto
  cases x with
  | nil =>
    wp_auto
    iapply HΦ
    ipureintro
    simp
  | ok ii =>
    obtain ⟨ty, v⟩ := ii
    wp_auto
    simp only [tsc_method1]
    repeat' (first | wp_if_destruct | wp_auto | simp only [tsc_method1])
    all_goals (iapply HΦ; ipureintro)
    all_goals simp_all [HasFmtSig, formatSig, noArgStringSig]

/-- The helper `fmt.inert`: whether Go formats the argument under any directive calling none of
its methods and reading no memory (`InertTy`). -/
theorem wp_inert (x : GoInterface) :
    {{ (True : IProp GF) }}
      (App (Val inert) (Val #x))
    {{ (b : Bool), RET #b;
        ⌜b = true ↔ (x = interface.nil ∨ ∃ ii, x = interface.ok ii ∧ InertTy ii.ty)⌝ }} := by
  iintro %Φ - HΦ
  unfold inert
  wp_auto
  cases x with
  | nil =>
    wp_auto
    iapply HΦ
    ipureintro
    simp
  | ok ii =>
    wp_auto
    wp_apply wp_isBasic as %b1 %Hb1
    cases b1
    case true =>
      wp_auto
      iapply HΦ
      ipureintro
      obtain ⟨_, ⟨⟩, hb⟩ := Hb1.1 rfl
      simp only [true_iff]
      exact .inr ⟨_, rfl, .inl hb⟩
    wp_auto
    wp_apply wp_hasFmtMethod as %b2 %Hb2
    cases b2
    case true =>
      wp_auto
      iapply HΦ
      ipureintro
      obtain ⟨_, ⟨⟩, hm⟩ := Hb2.1 rfl
      simp only [Bool.false_eq_true, false_iff, not_or, reduceCtorEq, not_false_eq_true,
        true_and, not_exists, not_and]
      rintro _ ⟨⟩ (hb | ⟨hn, -⟩)
      · exact absurd (Hb1.2 ⟨_, rfl, hb⟩) (by simp)
      · exact hn hm
    wp_auto
    wp_apply wp_isStrKind as %b3 %Hb3
    cases b3
    case true =>
      wp_auto
      iapply HΦ
      ipureintro
      obtain ⟨_, ⟨⟩, hs⟩ := Hb3.1 rfl
      simp only [true_iff]
      exact .inr ⟨_, rfl, .inr ⟨fun h => absurd (Hb2.2 ⟨_, rfl, h⟩) (by simp), .inl hs⟩⟩
    wp_auto
    wp_apply wp_isIntKind as %b4 %Hb4
    iapply HΦ
    ipureintro
    cases b4
    · simp only [Bool.false_eq_true, false_iff, not_or, reduceCtorEq, not_false_eq_true,
        true_and, not_exists, not_and]
      rintro _ ⟨⟩ (hb | ⟨-, hs | hi⟩)
      · exact absurd (Hb1.2 ⟨_, rfl, hb⟩) (by simp)
      · exact absurd (Hb3.2 ⟨_, rfl, hs⟩) (by simp)
      · exact absurd (Hb4.2 ⟨_, rfl, hi⟩) (by simp)
    · obtain ⟨_, ⟨⟩, hi⟩ := Hb4.1 rfl
      simp only [true_iff]
      exact .inr ⟨_, rfl, .inr ⟨fun h => absurd (Hb2.2 ⟨_, rfl, h⟩) (by simp), .inr hi⟩⟩

/-- A well-formed argument is inert. -/
theorem inertTy_of_argWf {ii : GoInterfaceOk} (h : ArgWf ii) : InertTy ii.ty := by
  have hns : ∀ t, NoFmtMethods t → ¬ HasFmtSig t := by
    rintro t ⟨h1, h2, h3, h4⟩ (h | h | h | h)
    · rw [h1] at h; cases h
    · rw [h2] at h; cases h
    · rw [h3] at h; cases h
    · rw [h4] at h; cases h
  rcases h.2.2 with hb | (hi | ⟨hi, hm⟩) | ⟨hs | ⟨-, hu, hm⟩, -⟩
  · exact .inl hb
  · exact .inl (.inr (.inr (.inl hi)))
  · exact .inr ⟨hns _ hm, .inr hi⟩
  · exact .inl (.inl hs)
  · exact .inr ⟨hns _ hm, .inl hu⟩

/-- The helper `fmt.allInert`, of arguments that are all `nil` or well-formed: `true`. -/
theorem wp_allInert (sl : GoSlice) (xs : List GoInterface) (dq : DFrac) (Hxs : ArgsWf xs) :
    {{ (sl ↦*{dq} xs : IProp GF) }}
      (App (Val allInert) (Val #sl))
    {{ RET #true; sl ↦*{dq} xs }} := by
  iintro %Φ Hs HΦ
  unfold allInert
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hs
  ihave IH : iprop(∃ (n : w64) (xv : GoInterface),
      "i" ∷ i_ptr ↦ n ∗
      "x" ∷ x_ptr ↦ xv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (xs.length : Int)⌝) $$ [i x]
  · iexists _, _
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < xs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, xs[(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z n) xs dq x Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx
    wp_apply wp_inert as %b %Hb
    have Hin : b = true := by
      rw [Hb]
      cases x with
      | nil => exact .inl rfl
      | ok ii => exact .inr ⟨ii, rfl, inertTy_of_argWf (Hxs ii (List.mem_of_getElem? Hx))⟩
    subst Hin
    wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  · iapply HΦ
    iframe

set_option maxHeartbeats 4000000 in
/-- The helper `fmt.parseDirective`: at `format[i]`, after a `%`, the directive as
`fmtDirectivesAux` reads it from the flags phase: not followed (`ok` false: a `*` width or
precision, an argument index, more than `maxNumDigits` digits), the end of the format inside the
directive (`verb` negative: no directive), or its verb and `%#v`/`%#w`, and the index after it. -/
theorem wp_parseDirective (format : GoString) (i : w64)
    (Hi : 0 ≤ sint.Z i ∧ sint.Z i ≤ (format.length : Int)) (Hlen : (format.length : Int) < 2 ^ 63) :
    {{ (True : IProp GF) }}
      (App (App (Val parseDirective) (Val #format)) (Val #i))
    {{ (verb : w64) (sharpV : Bool) (next : w64) (ok : Bool),
        RET (PairV (PairV (PairV #verb #sharpV) #next) #ok);
        ⌜(ok = false → fmtDirectivesAux (some (false, .flags)) (format.drop (sint.nat i)) = none) ∧
        (ok = true → sint.Z i ≤ sint.Z next ∧ sint.Z next ≤ (format.length : Int) ∧
          (sint.Z verb < 0 →
            fmtDirectivesAux (some (false, .flags)) (format.drop (sint.nat i)) = some [] ∧
            sint.Z next = (format.length : Int)) ∧
          (0 ≤ sint.Z verb → sint.Z verb < 256 ∧ sint.Z i < sint.Z next ∧
            (sharpV = true → W8 (sint.Z verb) = W8 118 ∨ W8 (sint.Z verb) = W8 119) ∧
            fmtDirectivesAux (some (false, .flags)) (format.drop (sint.nat i)) =
              dirCons (W8 (sint.Z verb)) sharpV
                (fmtDirectivesAux none (format.drop (sint.nat next)))))⌝ }} := by
  iintro %Φ - HΦ
  unfold parseDirective
  wp_auto
  ihave IH : iprop(∃ (iv : w64) (sh : Bool) (ph nv : w64),
      "i" ∷ i_ptr ↦ iv ∗ "sharp" ∷ sharp_ptr ↦ sh ∗ "phase" ∷ phase_ptr ↦ ph ∗ "n" ∷ n_ptr ↦ nv ∗
      "%Hiv" ∷ ⌜sint.Z i ≤ sint.Z iv ∧ sint.Z iv ≤ (format.length : Int)⌝ ∗
      "%Hph" ∷ ⌜(sint.Z ph = 0 ∨ sint.Z ph = 1 ∨ sint.Z ph = 2) ∧ 0 ≤ sint.Z nv ∧ sint.Z nv ≤ 7⌝ ∗
      "%Haux" ∷ ⌜fmtDirectivesAux (some (false, .flags)) (format.drop (sint.nat i)) =
        fmtDirectivesAux (some (sh, dirPh ph nv)) (format.drop (sint.nat iv))⌝) $$ [i sharp phase n]
  · iexists _, _, _, _
    iframe
    ipureintro
    rw [show zero_val w64 = W64 0 from rfl, show zero_val Bool = false from rfl]
    refine ⟨⟨by word, by word⟩, ⟨by left; rfl, by word, by word⟩, ?_⟩
    simp [dirPh]
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hflen
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat iv < format.length := by word
    obtain ⟨c, Hc, Hdrop⟩ : ∃ c, format[sint.nat iv]? = some c ∧
        format.drop (sint.nat iv) = c :: format.drop (sint.nat iv + 1) :=
      ⟨_, List.getElem?_eq_getElem Hlt, List.drop_eq_getElem_cons Hlt⟩
    rw [if_pos (show 0 ≤ sint.Z iv by word), Hc]
    obtain ⟨hph, hn0, hn7⟩ := Hph
    -- the arithmetic the branches need, once (no `word` in the branches)
    obtain ⟨hA, hB, hC, hD, hG, hG2⟩ := parseDirective_arith format i iv Hi Hlen Hiv Hlt
    obtain ⟨hN, hN'⟩ := parseDirective_digits nv hn0 hn7
    have hE : sint.Z (W64 (uint.Z c)) = uint.Z c := sint_Z_W64_byte c
    have hF : 0 ≤ uint.Z c ∧ uint.Z c < 256 := uint_Z_byte_bounds c
    have hph' := phase_cases ph hph
    clear hph
    rcases hph' with rfl | rfl | rfl
    all_goals
      simp only [dirPh_zero, dirPh_one, dirPh_two] at Haux
      rw [Hdrop] at Haux
      clear Hc Hdrop
      wp_auto
      repeat' (first | wp_if_destruct | wp_auto |
        (wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-))
    all_goals first
      | (exfalso; revert Hif; simp; done)
      | (exfalso; clear Hif; rename_i h; revert h; simp; done)
      | (wp_for_post
         iapply HΦ
         ipureintro
         rw [Haux]
         clear Haux
         first
           | (constructor
              · intro _
                simp_all [fmtDirectivesAux]
              · intro h
                cases h
              done)
           | (have hx := hN' Hif
              constructor
              · intro _
                simp_all [fmtDirectivesAux, nat_lt_eq_false_of_le]
              · intro h
                cases h
              done)
           | (constructor
              · intro h
                cases h
              intro _
              simp only [sint_Z_W64_byte, W8_uint_Z, hA, hE]
              refine ⟨hB, hC, fun h => absurd h (Int.not_lt.2 hF.1), fun _ => ⟨hF.2, hD, ?_, ?_⟩⟩
              · simp_all
              · simp_all [fmtDirectivesAux, dirCons, nat_le_eq_false_of_lt, nat_lt_eq_false_of_le]))
      | (wp_for_post
         iframe
         iexists _, _, _, _
         iframe
         ipureintro
         simp only [sint_nat_W64_one, sint_nat_W64_zero, show sint.Z (W64 1) = 1 from rfl,
           show sint.Z (W64 0) = 0 from rfl, show sint.Z (W64 2) = 2 from rfl]
         rw [Haux, hA]
         clear Haux
         simp only [dirPh_zero, dirPh_one, dirPh_two, sint_nat_W64_one, sint_nat_W64_zero]
         simp_all [fmtDirectivesAux])
  · have Hnot : ¬ sint.Z iv < sint.Z (W64 format.length) := fun h => Hif (by rw [decide_eq_true h])
    have Hend : sint.nat iv = format.length := by word
    rw [Hend, List.drop_length] at Haux
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    ipureintro
    constructor
    · intro h
      cases h
    intro _
    refine ⟨by word, by word, fun _ => ⟨?_, by word⟩, fun h => absurd h (by word)⟩
    rw [Haux]
    simp [fmtDirectivesAux]

/-- The helper `fmt.visitKind`, for an argument of integer or string kind: returns (Go prints it by
reflection, calling none of its methods, reading no memory). -/
theorem wp_visitKind (x : GoInterface)
    (Hx : ∃ ii, x = interface.ok ii ∧ (underlying ii.ty = go.string ∨ IsIntType (underlying ii.ty))) :
    {{ (True : IProp GF) }}
      (App (Val visitKind) (Val #x))
    {{ RET #(); True }} := by
  iintro %Φ - HΦ
  unfold visitKind
  wp_auto
  wp_apply wp_isStrKind as %b1 %Hb1
  cases b1
  case true =>
    wp_auto
    iapply HΦ
    itrivial
  wp_auto
  wp_apply wp_isIntKind as %b2 %Hb2
  cases b2
  case true =>
    wp_auto
    iapply HΦ
    itrivial
  exfalso
  obtain ⟨ii, rfl, hs | hi⟩ := Hx
  · exact absurd (Hb1.2 ⟨ii, rfl, hs⟩) (by simp)
  · exact absurd (Hb2.2 ⟨ii, rfl, hi⟩) (by simp)

/-- The method verbs of `doPrintf`'s mode: `Errorf`'s (`w` included) when it wraps errors. -/
def modeVerbs (wrapErrs : Bool) : List w8 := if wrapErrs then errorfVerbs else methodVerbs

theorem modeVerbs_false : modeVerbs false = methodVerbs := rfl
theorem modeVerbs_true : modeVerbs true = errorfVerbs := rfl

/-- A slice type has no methods (`go.NoMethods.slice`). -/
theorem methodSet_SliceType (t : go.GoType) (m : GoString) :
    methodSet (go.SliceType t) !! m = none := by
  have h := (go.InterfaceSemantics.method_set_no_methods (go.SliceType t)).method_set_is m
  simpa [go.methodSetLookup] using h

/-- A slice type is its own underlying type. -/
theorem underlying_SliceType (t : go.GoType) : underlying (go.SliceType t) = go.SliceType t :=
  (go.underlying_not_named (t := go.SliceType t)).is_underlying

/-- A type of string or integer kind is no slice type. -/
theorem ne_SliceType_of_kind {T : go.GoType} (t : go.GoType)
    (h : underlying T = go.string ∨ IsIntType (underlying T)) : T ≠ go.SliceType t := by
  rintro rfl
  rw [underlying_SliceType] at h
  simp [IsIntType, go.string, go.int, go.int64, go.int32, go.int16, go.int8, go.uint, go.uint64,
    go.uint32, go.uint16, go.uint8] at h

/-- A type with a method is no slice type. -/
theorem ne_SliceType_of_method {T : go.GoType} (t : go.GoType) {m : GoString} {s : go.signature}
    (h : methodSet T !! m = some s) : T ≠ go.SliceType t := by
  rintro rfl
  rw [methodSet_SliceType] at h
  cases h

/-- A well-formed argument's type is no slice type: a predeclared basic type, or one of integer or
string kind. -/
theorem ne_SliceType_of_argWf {ii : GoInterfaceOk} (t : go.GoType) (h : ArgWf ii) :
    ii.ty ≠ go.SliceType t := by
  intro he
  rcases h.2.2 with hb | (hi | ⟨hi, -⟩) | ⟨hs | ⟨-, hu, -⟩, -⟩ <;>
    simp_all [IsBasicType, IsIntType, underlying_SliceType, go.string, go.bool, go.int, go.int64,
      go.int32, go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8, go.uintptr,
      go.float32, go.float64]

set_option maxHeartbeats 4000000 in
/-- The helper `fmt.visitArg`: for an argument `argOkAt` its directive (`verb`, `sharpV`), calls
what Go's `printArg` calls of it (its `Error()` or `String()`, or nothing), and returns. -/
theorem wp_visitArg (x : GoInterface) (verb : w8) (sharpV wrapErrs : Bool)
    (Hsv : sharpV = true → verb = W8 118 ∨ verb = W8 119) :
    {{ argOkAt (GF := GF) (modeVerbs wrapErrs) ⟨verb, sharpV⟩ x }}
      (App (App (App (App (Val visitArg) (Val #x)) (Val #verb)) (Val #sharpV)) (Val #wrapErrs))
    {{ RET #(); True }} := by
  cases x with
  | nil =>
    iintro %Φ - HΦ
    unfold visitArg
    wp_auto
    iapply HΦ
    itrivial
  | ok ii =>
    simp only [argOkAt]
    iintro %Φ Hx HΦ
    unfold visitArg
    wp_auto
    -- `%T` and `%p`: nothing
    wp_if_destruct
    · iapply HΦ; itrivial
    have hnT := Hif
    wp_if_destruct
    · iapply HΦ; itrivial
    have hnP := Hif
    -- a predeclared basic type: nothing
    wp_apply wp_isBasic as %b %Hb
    cases b
    case true =>
      wp_auto
      iapply HΦ
      itrivial
    have hnb : ¬ IsBasicType ii.ty := fun h => absurd (Hb.2 ⟨ii, rfl, h⟩) (by simp)
    clear Hb
    wp_auto
    icases Hx with (%Hwf | %Hni | ⟨%Hm, Hok⟩ | %HT | %Hp)
    · -- a type without formatting methods, of integer or string kind
      have hnf : NoFmtMethods ii.ty ∧ (underlying ii.ty = go.string ∨ IsIntType (underlying ii.ty)) := by
        rcases Hwf.2.2 with hb | (hi | ⟨hi, hm⟩) | ⟨hs | ⟨-, hu, hm⟩, -⟩
        · exact absurd hb hnb
        · exact absurd (Or.inr (Or.inr (Or.inl hi))) hnb
        · exact ⟨hm, .inr hi⟩
        · exact absurd (Or.inl hs) hnb
        · exact ⟨hm, .inl hu⟩
      obtain ⟨⟨hF, hG, hE, hS⟩, hk⟩ := hnf
      have hnB := ne_SliceType_of_kind go.byte hk
      repeat' (first | wp_if_destruct | wp_auto | simp only [tsc_method1, tsc_error, hF, hG, hE, hS,
        hnB, ↓reduceIte, reduceCtorEq, decide_false] | wp_apply (wp_visitKind _ ⟨_, rfl, hk⟩))
      all_goals first
        | (iapply HΦ; itrivial)
        | (exfalso; simp_all; done)
    · -- an integer kind with `Error()`/`String()` under a verb that calls neither
      obtain ⟨hnm, hk, hF, -⟩ := Hni
      have hnB := ne_SliceType_of_kind go.byte (.inr hk)
      cases wrapErrs <;> simp only [modeVerbs, Bool.false_eq_true, ↓reduceIte] at hnm
      all_goals
        repeat' (first | wp_if_destruct | wp_auto | simp only [tsc_method1, tsc_error, hF,
          hnB, ↓reduceIte, reduceCtorEq, decide_false] | wp_apply (wp_visitKind _ ⟨_, rfl, .inr hk⟩))
      all_goals first
        | (iapply HΦ; itrivial)
        | (exfalso; simp_all [methodVerbs, errorfVerbs]; done)
    · -- a method verb: `Error()` or `String()`
      obtain ⟨hmv, rfl, hw⟩ := Hm
      iunfold argOk at Hok
      icases Hok with (%Hwf | ⟨#HE, %hE⟩ | ⟨#HS, %hS⟩)
      · have hnf : NoFmtMethods ii.ty ∧
            (underlying ii.ty = go.string ∨ IsIntType (underlying ii.ty)) := by
          rcases Hwf.2.2 with hb | (hi | ⟨hi, hm⟩) | ⟨hs | ⟨-, hu, hm⟩, -⟩
          · exact absurd hb hnb
          · exact absurd (Or.inr (Or.inr (Or.inl hi))) hnb
          · exact ⟨hm, .inr hi⟩
          · exact absurd (Or.inl hs) hnb
          · exact ⟨hm, .inl hu⟩
        obtain ⟨⟨hF, hG, hE, hS⟩, hk⟩ := hnf
        have hnB := ne_SliceType_of_kind go.byte hk
        repeat' (first | wp_if_destruct | wp_auto | simp only [tsc_method1, tsc_error, hF, hG, hE, hS,
          hnB, ↓reduceIte, reduceCtorEq, decide_false] | wp_apply (wp_visitKind _ ⟨_, rfl, hk⟩))
        all_goals first
          | (iapply HΦ; itrivial)
          | (exfalso; simp_all; done)
      · obtain ⟨hF, hE⟩ := hE
        have hnB := ne_SliceType_of_method go.byte hE
        iunfold stringMethodSpec at HE
        cases wrapErrs <;> simp only [modeVerbs, Bool.false_eq_true, ↓reduceIte] at hmv
        all_goals
          repeat' (first | wp_if_destruct | wp_auto | simp only [tsc_method1, tsc_error, hF, hE,
            hnB, ↓reduceIte, noArgStringSig, reduceCtorEq, decide_false, decide_true] |
            (wp_bind (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #()))
             iapply HE
             inext
             iintro %_))
        all_goals first
          | (iapply HΦ; itrivial)
          | (exfalso; simp_all [methodVerbs, errorfVerbs]; done)
      · obtain ⟨hF, hE, hS, hR⟩ := hS
        have hnB := ne_SliceType_of_method go.byte hS
        iunfold stringMethodSpec at HS
        cases wrapErrs <;> simp only [modeVerbs, Bool.false_eq_true, ↓reduceIte] at hmv
        all_goals
          repeat' (first | wp_if_destruct | wp_auto | simp only [tsc_method1, tsc_error, hF, hE, hS,
            hR, hnB, ↓reduceIte, noArgStringSig, reduceCtorEq, decide_false, decide_true] |
            (wp_bind (App (Val #(methods ii.ty go!"String" ii.v)) (Val #()))
             iapply HS
             inext
             iintro %_))
        all_goals first
          | (iapply HΦ; itrivial)
          | (exfalso; simp_all [methodVerbs, errorfVerbs]; done)
    · exact absurd HT hnT
    · exact absurd Hp.1 hnP

theorem argsOkAt_nil_args (mv : List w8) (ds : List Directive) :
    ⊢ argsOkAt (GF := GF) mv ds [] := by
  cases ds <;> (unfold argsOkAt; itrivial)

theorem argOkAt_of_argWf (mv : List w8) (d : Directive) (x : GoInterface)
    (h : ∀ ii, x = interface.ok ii → ArgWf ii) : ⊢ argOkAt (GF := GF) mv d x := by
  cases x with
  | nil => unfold argOkAt; itrivial
  | ok ii => unfold argOkAt; ileft; ipureintro; exact h ii rfl

set_option maxHeartbeats 4000000 in
/-- The helper `fmt.visitRest`: from the `%`-or-literal at `format[i]` and the argument `k` on,
calls what Go calls of each argument (its directive's, or `%v` for those left over), for arguments
`argsOk` the directives left; returns the arguments of the `%w` directives (`wrapArgsFrom`), or
gives up (`unknown`) at a directive `fmtDirectives` refuses, every argument being `ArgWf`. -/
theorem wp_visitRest (format : GoString) (i : w64) (sl : GoSlice) (xs : List GoInterface)
    (dq : DFrac) (k : w64) (wrapErrs : Bool)
    (Hi : 0 ≤ sint.Z i ∧ sint.Z i ≤ (format.length : Int)) (Hlen : (format.length : Int) < 2 ^ 63)
    (Hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ (xs.length : Int)) :
    {{ sl ↦*{dq} xs ∗
        (⌜ArgsWf xs⌝ ∨ ∃ ds, ⌜fmtDirectivesAux none (format.drop (sint.nat i)) = some ds⌝ ∗
          argsOkAt (GF := GF) (modeVerbs wrapErrs) ds (xs.drop (sint.nat k))) }}
      (App (App (App (App (App (Val visitRest) (Val #format)) (Val #i)) (Val #sl)) (Val #k))
        (Val #wrapErrs))
    {{ (wsl : GoSlice) (unknown : Bool), RET (PairV #wsl #unknown);
        sl ↦*{dq} xs ∗ ∃ ws : List w64, wsl ↦* ws ∗
        ⌜(unknown = true → ArgsWf xs ∧ fmtDirectivesAux none (format.drop (sint.nat i)) = none) ∧
         (unknown = false → ∃ ds, fmtDirectivesAux none (format.drop (sint.nat i)) = some ds ∧
            ws = (wrapArgsFrom (sint.nat k) ds xs.length).map (fun j : Nat => W64 (j : Int)))⌝ }} := by
  iintro %Φ ⟨Hsl, Hargs⟩ HΦ
  unfold visitRest
  wp_auto
  ihave %Hxlen := ownSlice_len $$ Hsl
  ihave Hws0 := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
  ihave Hwc0 := ownSliceCap_nil (V := w64) (GF := GF)
  ihave IH : iprop(∃ (iv kv : w64) (wsl : GoSlice) (ws : List w64) (pre : List Directive),
      "i" ∷ i_ptr ↦ iv ∗ "argNum" ∷ argNum_ptr ↦ kv ∗ "wrapped" ∷ wrapped_ptr ↦ wsl ∗
      "Hws" ∷ wsl ↦* ws ∗ "Hwc" ∷ ownSliceCap w64 wsl (DFrac.own 1) ∗
      "%Hiv" ∷ ⌜sint.Z i ≤ sint.Z iv ∧ sint.Z iv ≤ (format.length : Int)⌝ ∗
      "%Hkv" ∷ ⌜sint.Z k ≤ sint.Z kv ∧ sint.Z kv ≤ (xs.length : Int) ∧
        sint.nat kv = min (sint.nat k + pre.length) xs.length⌝ ∗
      "%Hpre" ∷ ⌜fmtDirectivesAux none (format.drop (sint.nat i)) =
        (pre ++ ·) <$> fmtDirectivesAux none (format.drop (sint.nat iv))⌝ ∗
      "%Hwsv" ∷ ⌜ws = (wrapArgsFrom (sint.nat k) pre xs.length).map (fun j : Nat => W64 (j : Int))⌝ ∗
      "Hargs" ∷ (⌜ArgsWf xs⌝ ∨ ∃ ds, ⌜fmtDirectivesAux none (format.drop (sint.nat iv)) = some ds⌝ ∗
          argsOkAt (GF := GF) (modeVerbs wrapErrs) ds (xs.drop (sint.nat kv))))
      $$ [i argNum wrapped Hws0 Hwc0 Hargs]
  · iexists i, k, slice.nil, [], []
    rw [show zero_val GoSlice = slice.nil from rfl]
    iframe
    isplitr
    · iexact Hws0
    isplitr
    · iexact Hwc0
    ipureintro
    refine ⟨⟨by word, by word⟩, ⟨by word, by word, by simp; word⟩, by simp, by simp [wrapArgsFrom]⟩
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hflen
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat iv < format.length := by word
    obtain ⟨c, Hc, Hdrop⟩ : ∃ c, format[sint.nat iv]? = some c ∧
        format.drop (sint.nat iv) = c :: format.drop (sint.nat iv + 1) :=
      ⟨_, List.getElem?_eq_getElem Hlt, List.drop_eq_getElem_cons Hlt⟩
    have hiv1 : sint.nat (iv + W64 1) = sint.nat iv + 1 := by word
    rw [if_pos (show 0 ≤ sint.Z iv by word), Hc]
    by_cases hc37 : c ≠ W8 37
    · -- a literal byte
      wp_auto
      simp only [hc37, decide_false, Bool.not_false]
      wp_auto
      have hlit : fmtDirectivesAux none (format.drop (sint.nat iv)) =
          fmtDirectivesAux none (format.drop (sint.nat (iv + W64 1))) := by
        rw [Hdrop, hiv1]; exact fmtDirectivesAux_lit _ hc37
      wp_for_post
      iframe
      iexists _, _, _, _, pre
      rw [← hlit]
      iframe
      ipureintro
      exact ⟨⟨by word, by word⟩, Hkv, Hpre, Hwsv⟩
    rw [Classical.not_not] at hc37
    subst hc37
    wp_auto
    try simp only [_root_.decide_true, Bool.not_true]
    try wp_auto
    have hpct : fmtDirectivesAux none (format.drop (sint.nat iv)) =
        fmtDirectivesAux (some (false, .flags)) (format.drop (sint.nat (iv + W64 1))) := by
      rw [Hdrop, hiv1]; exact fmtDirectivesAux_pct _
    wp_apply wp_parseDirective format (iv + W64 1) ⟨by word, by word⟩ Hlen
      as %verb %sharpV %next %ok %Hpd
    cases ok
    · -- a directive the model does not follow: every argument is `ArgWf`
      have hnone : fmtDirectivesAux none (format.drop (sint.nat iv)) = none := by
        rw [hpct]; exact Hpd.1 rfl
      ihave %Hwf : iprop(⌜ArgsWf xs⌝) $$ [Hargs]
      · icases Hargs with (%Hwf | ⟨%ds, %Hds, -⟩)
        · ipureintro; exact Hwf
        · rw [hnone] at Hds; cases Hds
      wp_auto
      wp_apply wp_allInert sl xs dq Hwf $$ [$Hsl] as Hsl
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      refine ⟨fun _ => ⟨Hwf, by rw [Hpre, hnone]; rfl⟩, fun h => nomatch h⟩
    obtain ⟨hn1, hn2, hneg, hpos⟩ := Hpd.2 rfl
    clear Hpd
    wp_auto
    by_cases hvn : sint.Z verb < 0
    · -- the format ends inside the directive: no directive
      obtain ⟨hnil, hnext⟩ := hneg hvn
      have haux : fmtDirectivesAux none (format.drop (sint.nat iv)) =
          fmtDirectivesAux none (format.drop (sint.nat next)) := by
        rw [hpct, hnil, show sint.nat next = format.length by word, List.drop_length]
        simp [fmtDirectivesAux]
      have hv0 : sint.Z verb < sint.Z (W64 0) := by word
      simp only [hv0, _root_.decide_true]
      wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _, pre
      rw [← haux]
      iframe
      ipureintro
      exact ⟨⟨by word, by word⟩, Hkv, Hpre, Hwsv⟩
    have hv0 : ¬ sint.Z verb < sint.Z (W64 0) := by word
    simp only [hv0, decide_false]
    obtain ⟨hv256, hnext, hsv, heq⟩ := hpos (by word)
    clear hneg hpos
    have hvpos : 0 ≤ sint.Z verb := by word
    wp_auto
    by_cases hv37 : verb = W64 37
    · -- `%%` (after flags, width or precision): no argument
      have h37 : W8 (sint.Z verb) = W8 37 := (w8_verb_eq verb hvpos hv256 37 (by decide)).2 hv37
      have haux : fmtDirectivesAux none (format.drop (sint.nat iv)) =
          fmtDirectivesAux none (format.drop (sint.nat next)) := by
        rw [hpct, heq, dirCons, if_pos h37]
      subst hv37
      simp only [_root_.decide_true]
      wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _, pre
      rw [← haux]
      iframe
      ipureintro
      exact ⟨⟨by word, by word⟩, Hkv, Hpre, Hwsv⟩
    have hn37 : W8 (sint.Z verb) ≠ W8 37 := fun h =>
      hv37 ((w8_verb_eq verb hvpos hv256 37 (by decide)).1 h)
    simp only [hv37, decide_false]
    have haux : fmtDirectivesAux none (format.drop (sint.nat iv)) =
        (⟨W8 (sint.Z verb), sharpV⟩ :: ·) <$> fmtDirectivesAux none (format.drop (sint.nat next)) := by
      rw [hpct, heq, dirCons, if_neg hn37]
    have Hpre' : fmtDirectivesAux none (format.drop (sint.nat i)) =
        ((pre ++ [⟨W8 (sint.Z verb), sharpV⟩]) ++ ·) <$>
          fmtDirectivesAux none (format.drop (sint.nat next)) := by
      rw [Hpre, haux]
      cases fmtDirectivesAux none (format.drop (sint.nat next)) <;> simp
    wp_auto
    wp_if_destruct
    · -- no argument left (`%!v(MISSING)`)
      have Hge : (xs.length : Int) ≤ sint.Z kv := by word
      have hkvn : sint.nat kv = xs.length := by word
      have hkpre : xs.length ≤ sint.nat k + pre.length := by
        have := Hkv.2.2; omega
      ihave Hargs' : iprop(⌜ArgsWf xs⌝ ∨
          ∃ ds, ⌜fmtDirectivesAux none (format.drop (sint.nat next)) = some ds⌝ ∗
            argsOkAt (GF := GF) (modeVerbs wrapErrs) ds (xs.drop (sint.nat kv))) $$ [Hargs]
      · icases Hargs with (%Hwf | ⟨%ds, %Hds, Hds⟩)
        · ileft; ipureintro; exact Hwf
        · iright
          rw [haux] at Hds
          obtain ⟨ds', Hds', rfl⟩ : ∃ ds', fmtDirectivesAux none (format.drop (sint.nat next)) = some ds' ∧
              ds = ⟨W8 (sint.Z verb), sharpV⟩ :: ds' := by
            revert Hds
            cases fmtDirectivesAux none (format.drop (sint.nat next)) <;> simp
            exact fun h => h.symm
          iexists ds'
          isplitr
          · ipureintro; exact Hds'
          rw [List.drop_eq_nil_of_le (show xs.length ≤ sint.nat kv by omega)]
          iapply argsOkAt_nil_args
      wp_for_post
      iframe
      iexists _, _, _, _, (pre ++ [⟨W8 (sint.Z verb), sharpV⟩])
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ⟨Hkv.1, Hkv.2.1, ?_⟩, Hpre', ?_⟩
      · rw [Hkv.2.2, List.length_append]; simp only [List.length_singleton]; omega
      · rw [Hwsv, wrapArgsFrom_append]
        simp only [show ¬ (sint.nat k + pre.length < xs.length) by omega, _root_.and_false,
          ↓reduceIte, List.append_nil]
    -- an argument: its directive
    have Hif' : ¬ (xs.length : Int) ≤ sint.Z kv := by word
    have Hklt : sint.nat kv < xs.length := by word
    have Hkvs : sint.nat kv = sint.nat k + pre.length := by have := Hkv.2.2; omega
    obtain ⟨x, Hx, Hdropk⟩ : ∃ x, xs[sint.nat kv]? = some x ∧
        xs.drop (sint.nat kv) = x :: xs.drop (sint.nat kv + 1) :=
      ⟨_, List.getElem?_eq_getElem Hklt, List.drop_eq_getElem_cons Hklt⟩
    have Hkv1 : sint.nat (kv + W64 1) = sint.nat kv + 1 := by word
    ihave ⟨Hxok, Hargs'⟩ : iprop(argOkAt (GF := GF) (modeVerbs wrapErrs) ⟨W8 (sint.Z verb), sharpV⟩ x ∗
        (⌜ArgsWf xs⌝ ∨ ∃ ds, ⌜fmtDirectivesAux none (format.drop (sint.nat next)) = some ds⌝ ∗
          argsOkAt (GF := GF) (modeVerbs wrapErrs) ds (xs.drop (sint.nat (kv + W64 1))))) $$ [Hargs]
    · icases Hargs with (%Hwf | ⟨%ds, %Hds, Hds⟩)
      · isplitl []
        · iapply argOkAt_of_argWf
          intro ii h; exact Hwf ii (h ▸ List.mem_of_getElem? Hx)
        · ileft; ipureintro; exact Hwf
      · rw [haux] at Hds
        obtain ⟨ds', Hds', rfl⟩ : ∃ ds', fmtDirectivesAux none (format.drop (sint.nat next)) = some ds' ∧
            ds = ⟨W8 (sint.Z verb), sharpV⟩ :: ds' := by
          revert Hds
          cases fmtDirectivesAux none (format.drop (sint.nat next)) <;> simp
          exact fun h => h.symm
        rw [Hdropk]
        simp only [argsOkAt]
        icases Hds with ⟨Hd, Hds⟩
        iframe Hd
        iright
        iexists ds'
        isplitr
        · ipureintro; exact Hds'
        rw [Hkv1]
        iexact Hds
    have hwiff : W8 (sint.Z verb) = W8 119 ↔ verb = W64 119 :=
      w8_verb_eq verb hvpos hv256 119 (by decide)
    have hkvW : W64 ((sint.nat k + pre.length : Nat) : Int) = kv := by rw [← Hkvs]; word
    by_cases hw : verb = W64 119
    · have hd119 : W8 (sint.Z verb) = W8 119 := hwiff.2 hw
      simp only [hw, _root_.decide_true]
      wp_auto
      wp_apply wp_slice_literal (V := w64) [kv]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hws $Hwc $Hsl2] as %wsl' ⟨Hws, Hwc, -⟩
      try wp_auto
      simp only [show 0 ≤ sint.Z kv ∧ sint.Z kv < sint.Z sl.len from ⟨by word, by word⟩,
        and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sl (sint.Z kv) xs dq x (by word) $$ [Hsl] with Hsl
      · iframe; ipureintro; exact Hx
      rw [← hw]
      wp_apply (wp_visitArg x (W8 (sint.Z verb)) sharpV wrapErrs hsv) $$ [$Hxok]
      wp_for_post
      iframe
      iexists _, _, _, _, (pre ++ [⟨W8 (sint.Z verb), sharpV⟩])
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ⟨by word, by word, ?_⟩, Hpre', ?_⟩
      · rw [Hkv1, List.length_append]; simp only [List.length_singleton]; omega
      · rw [Hwsv, wrapArgsFrom_append]
        simp only [hd119, show sint.nat k + pre.length < xs.length by omega, and_self, ↓reduceIte,
          List.map_append, List.map_cons, List.map_nil, hkvW]
    · have hd119 : W8 (sint.Z verb) ≠ W8 119 := fun h => hw (hwiff.1 h)
      simp only [hw, decide_false]
      wp_auto
      simp only [show 0 ≤ sint.Z kv ∧ sint.Z kv < sint.Z sl.len from ⟨by word, by word⟩,
        and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sl (sint.Z kv) xs dq x (by word) $$ [Hsl] with Hsl
      · iframe; ipureintro; exact Hx
      wp_apply (wp_visitArg x (W8 (sint.Z verb)) sharpV wrapErrs hsv) $$ [$Hxok]
      wp_for_post
      iframe
      iexists _, _, _, _, (pre ++ [⟨W8 (sint.Z verb), sharpV⟩])
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ⟨by word, by word, ?_⟩, Hpre', ?_⟩
      · rw [Hkv1, List.length_append]; simp only [List.length_singleton]; omega
      · rw [Hwsv, wrapArgsFrom_append]
        simp only [hd119, _root_.false_and, ↓reduceIte, List.append_nil]
  · -- the end of the format: the arguments left over, under `%v`
    have Hnot : ¬ sint.Z iv < sint.Z (W64 format.length) := fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    have Hend : sint.nat iv = format.length := by word
    rw [Hend, List.drop_length] at Hpre
    rw [Hend, List.drop_length]
    have Hpre0 : fmtDirectivesAux none (format.drop (sint.nat i)) = some pre := by
      rw [Hpre]; simp [fmtDirectivesAux]
    wp_auto
    ihave IH2 : iprop(∃ kv' : w64, "argNum" ∷ argNum_ptr ↦ kv' ∗
        "%Hkv'" ∷ ⌜sint.Z kv ≤ sint.Z kv' ∧ sint.Z kv' ≤ (xs.length : Int)⌝ ∗
        "Hargs" ∷ (⌜ArgsWf xs⌝ ∨ argsOkAt (GF := GF) (modeVerbs wrapErrs) [] (xs.drop (sint.nat kv'))))
      $$ [argNum Hargs]
    · iexists kv
      iframe
      isplitr
      · ipureintro; exact ⟨by word, Hkv.2.1⟩
      icases Hargs with (%Hwf | ⟨%ds, %Hds, Hds⟩)
      · ileft; ipureintro; exact Hwf
      · iright
        simp only [fmtDirectivesAux, Option.some.injEq] at Hds
        subst Hds
        iexact Hds
    wp_for IH2
    wp_if_destruct
    · have Hklt : sint.nat kv' < xs.length := by word
      obtain ⟨x, Hx, Hdropk⟩ : ∃ x, xs[sint.nat kv']? = some x ∧
          xs.drop (sint.nat kv') = x :: xs.drop (sint.nat kv' + 1) :=
        ⟨_, List.getElem?_eq_getElem Hklt, List.drop_eq_getElem_cons Hklt⟩
      have Hkv1 : sint.nat (kv' + W64 1) = sint.nat kv' + 1 := by word
      ihave ⟨Hxok, Hargs'⟩ : iprop(argOkAt (GF := GF) (modeVerbs wrapErrs) ⟨W8 118, false⟩ x ∗
          (⌜ArgsWf xs⌝ ∨ argsOkAt (GF := GF) (modeVerbs wrapErrs) [] (xs.drop (sint.nat (kv' + W64 1)))))
        $$ [Hargs]
      · icases Hargs with (%Hwf | Hds)
        · isplitl []
          · iapply argOkAt_of_argWf
            intro ii h; exact Hwf ii (h ▸ List.mem_of_getElem? Hx)
          · ileft; ipureintro; exact Hwf
        · rw [Hdropk]
          simp only [argsOkAt]
          icases Hds with ⟨Hd, Hds⟩
          iframe Hd
          iright
          rw [Hkv1]
          iexact Hds
      simp only [show 0 ≤ sint.Z kv' ∧ sint.Z kv' < sint.Z sl.len from ⟨by word, by word⟩,
        and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sl (sint.Z kv') xs dq x (by word) $$ [Hsl] with Hsl
      · iframe; ipureintro; exact Hx
      wp_apply (wp_visitArg x (W8 118) false wrapErrs (fun h => nomatch h)) $$ [$Hxok]
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    · iapply HΦ
      iframe
      ipureintro
      constructor
      · intro h; cases h
      · intro _
        exact ⟨pre, Hpre0, Hwsv⟩

end wps

end fmt

end Perennial
