/-
Facts about the IEEE 754 float operations of the Go semantics
(`Perennial/Golang/Defn/Float.lean`): signs of conversions and comparisons with zero, and the
specs of the arithmetic operations (IEEE 754's result, any NaN if it is a NaN).
-/
module

public import Perennial.Golang.Defn.Float
public import Perennial.Golang.Theory.Auto

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

namespace ieee754
namespace Format
variable (f : Format)

theorem msb_pack (s : Bool) (E T : Nat) : (f.pack s E T).msb = s := by
  simp [pack, BitVec.msb_append]

/-- A rounding has the sign it is given: it is `±∞` or a finite number of that sign. -/
theorem round_cases (s : Bool) (m : Rat) :
    f.round s m = .inf s ∨ ∃ r, f.round s m = .finite s r := by
  unfold round
  dsimp only
  split
  · exact .inr ⟨_, rfl⟩
  · exact .inl rfl

/-- The bit pattern of a rounding has the rounding's sign. -/
theorem msb_encode_round (s : Bool) (m : Rat) (b : f.Bits)
    (h : f.encode (f.round s m) = some b) : b.msb = s := by
  rcases f.round_cases s m with hr | ⟨r, hr⟩ <;> rw [hr] at h <;> simp only [encode] at h
  · cases h; exact f.msb_pack ..
  · split at h <;> (cases h; exact f.msb_pack ..)

theorem msb_encode_ofInt_of_nonneg (n : Int) (h : 0 ≤ n) :
    ((f.encode (f.ofInt n)).getD 0).msb = false := by
  have : ¬ (n : Rat) < 0 := fun h' => (Rat.not_le.mpr h') (by exact_mod_cast h)
  rw [ofInt_unseal, ofIntDef, roundRat]
  simp only [this, decide_false, if_false]
  cases hb : f.encode (f.round false n) with
  | none => simp
  | some b => exact f.msb_encode_round false _ b hb

theorem pow2_nonneg (k : Int) : 0 ≤ pow2 k := by
  unfold pow2
  split
  · exact Rat.natCast_nonneg
  · exact Rat.le_of_lt (Rat.inv_pos.mpr (by
      have : (0 : Nat) < 2 ^ (-k).toNat := Nat.two_pow_pos _
      exact_mod_cast this))

/-- The value of a bit pattern with a clear sign bit: NaN, `+∞`, or a non-negative number. -/
theorem decode_of_msb_false (x : f.Bits) (h : x.msb = false) :
    f.decode x = .nan ∨ f.decode x = .inf false ∨ ∃ m, 0 ≤ m ∧ f.decode x = .finite false m := by
  unfold decode
  simp only [h]
  split
  · split
    · exact .inr (.inl rfl)
    · exact .inl rfl
  · split
    · exact .inr (.inr ⟨_, Rat.mul_nonneg Rat.natCast_nonneg (pow2_nonneg _), rfl⟩)
    · exact .inr (.inr ⟨_,
        Rat.mul_nonneg (by exact_mod_cast Rat.natCast_nonneg) (pow2_nonneg _), rfl⟩)

end Format
end ieee754

open ieee754

private theorem msb_false_of_toInt_nonneg {n : Nat} (x : BitVec n) (h : 0 ≤ x.toInt) :
    x.msb = false := by
  cases hm : x.msb
  · rfl
  · exact absurd (BitVec.toInt_neg_iff.mpr (BitVec.msb_eq_true_iff_two_mul_ge.mp hm)) (by omega)

/-! The sign facts that `counter.Add(v)`'s `v < 0` test needs (prometheus): `float64(n)` of a
non-negative integer has a clear sign bit (it is `+0` or positive), and a `float64` with a
clear sign bit (`+0`, a positive number, `+∞` or a NaN) is not below `+0`. -/

theorem int64ToFloat64_sign_clear (n : w64) (h : 0 ≤ sint.Z n) : 0 ≤ sint.Z (int64ToFloat64 n) :=
  BitVec.toInt_nonneg_of_msb_false (binary64.msb_encode_ofInt_of_nonneg _ h)
theorem uint64ToFloat64_sign_clear (n : w64) : 0 ≤ sint.Z (uint64ToFloat64 n) :=
  BitVec.toInt_nonneg_of_msb_false (binary64.msb_encode_ofInt_of_nonneg _ (by omega))
theorem int32ToFloat64_sign_clear (n : w32) (h : 0 ≤ sint.Z n) : 0 ≤ sint.Z (int32ToFloat64 n) :=
  BitVec.toInt_nonneg_of_msb_false (binary64.msb_encode_ofInt_of_nonneg _ h)
theorem uint32ToFloat64_sign_clear (n : w32) : 0 ≤ sint.Z (uint32ToFloat64 n) :=
  BitVec.toInt_nonneg_of_msb_false (binary64.msb_encode_ofInt_of_nonneg _ (by omega))

private theorem decode_zero64 : binary64.decode (W64 0) = .finite false 0 := by
  simp [Format.decode, binary64]

/-- `x < 0` (as `lt_float64` steps it: `Leb && !Eq`) is false for a `float64` `x` with a clear
sign bit. -/
theorem lt_zero_false_of_sign_clear (x : w64) (h : 0 ≤ sint.Z x) :
    (float64Leb x (W64 0) && !float64Eq x (W64 0)) = false := by
  have hd := binary64.decode_of_msb_false x (msb_false_of_toInt_nonneg x h)
  simp only [float64Leb, float64Eq, Format.leb_unseal, Format.eq_unseal, Format.lebDef,
    Format.eqDef, decode_zero64]
  rcases hd with hd | hd | ⟨m, hm, hd⟩ <;> rw [hd]
  · rfl
  · rfl
  · simp only [signed]
    by_cases h0 : m = 0
    · subst h0; decide
    · have : ¬ m ≤ 0 := fun h' => h0 (Rat.le_antisymm h' hm)
      simp [this]

/-- `x == x` unless `x` is a NaN. -/
theorem float64Eq_self (x : w64) : float64Eq x x = !float64IsNaN x := by
  simp only [float64Eq, float64IsNaN, Format.eq_unseal, Format.isNaN_unseal, Format.eqDef,
    Format.isNaNDef]
  cases binary64.decode x <;> simp

theorem float32Eq_self (x : w32) : float32Eq x x = !float32IsNaN x := by
  simp only [float32Eq, float32IsNaN, Format.eq_unseal, Format.isNaN_unseal, Format.eqDef,
    Format.isNaNDef]
  cases binary32.decode x <;> simp

/-- Every value has an encoding (NaN has many). -/
theorem float64Encodes_exists (d : FloatValue) : ∃ b, float64Encodes d b := by
  unfold float64Encodes Format.encodes
  cases h : binary64.encode d with
  | some b => exact ⟨b, rfl⟩
  | none => exact ⟨0x7FF8000000000000, by simp only; decide⟩
theorem float32Encodes_exists (d : FloatValue) : ∃ b, float32Encodes d b := by
  unfold float32Encodes Format.encodes
  cases h : binary32.encode d with
  | some b => exact ⟨b, rfl⟩
  | none => exact ⟨0x7FC00000, by simp only; decide⟩

open Perennial.go in
/-- `x < 0` of a `float64` `x` with a clear sign bit is `false`: the step of `x < 0`
(`go.lt_float64`) with `#false` for `#(float64Leb x 0 && !float64Eq x 0)`. -/
theorem lt_float64_zero_step_of_sign_clear [GooseExts] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions]
    [go.Float64Semantics] (x : w64) (h : 0 ≤ sint.Z x) :
    ⟦GoOp GoLt go.float64, (#x, #(W64 0))⟧ ⤳[under] #false := by
  have := go.lt_float64 x (W64 0)
  rwa [lt_zero_false_of_sign_clear x h] at this

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
variable {s : Stuckness} {E : CoPset}

/-- A Go instruction whose pure step is a relation: `op` applied to `arg` steps to any
`#(inj f)` with `P f` (and some `f` satisfies `P`). The float arithmetic rules have this
form (`go.plus_float64`, ...). -/
theorem wp_go_step_rel {V : Type} (inj : V → val) (op : GoInstruction) (arg : val)
    (P : V → Prop)
    (hop : ∀ e gs gs', IsGoStep op arg e gs gs' ↔ is_go_step_pure op arg e ∧ gs = gs')
    (hstep : is_go_step_pure op arg = fun e => ∃ f, e = Val (inj f) ∧ P f)
    (hP : ∃ f, P f) (Harg : arg.isPanic = false := by simp) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction op)) (Val arg)) @ s; E
    {{ (f : V), RET inj f; ⌜P f⌝ }} := by
  iintro %Φ _ HΦ
  obtain ⟨f0, hf0⟩ := hP
  iapply wp_GoInstruction' (s := s) (E := E) op arg Φ
    (fun gs => ⟨Val (inj f0), gs, (hop _ _ _).mpr ⟨by rw [hstep]; exact ⟨f0, rfl, hf0⟩, rfl⟩⟩)
    Harg
  inext
  iintro %e' %gs %gs' %Hstep _ Hctx
  obtain ⟨Hp, rfl⟩ := (hop _ _ _).mp Hstep
  rw [hstep] at Hp
  obtain ⟨f, rfl, Hf⟩ := Hp
  imodintro
  iframe Hctx
  iapply wp_value'
  iapply HΦ
  ipureintro; exact Hf

/-! The arithmetic operations of `float64` and `float32` (and of the named types whose
underlying type they are): the result `f` encodes IEEE 754's result value (`float64Encodes`:
its bit pattern, or any NaN if it is NaN). Use as `wp_apply wp_float64_add as %f Hf`. -/

theorem wp_float64_add {t : go.GoType} [t ↓u go.float64] (v1 v2 : w64) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoPlus t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w64), RET #f; ⌜float64Encodes (float64Add v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w64 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.plus_float64 v1 v2)
    (float64Encodes_exists _)

theorem wp_float64_sub {t : go.GoType} [t ↓u go.float64] (v1 v2 : w64) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoSub t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w64), RET #f; ⌜float64Encodes (float64Sub v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w64 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.sub_float64 v1 v2)
    (float64Encodes_exists _)

theorem wp_float64_mul {t : go.GoType} [t ↓u go.float64] (v1 v2 : w64) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoMul t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w64), RET #f; ⌜float64Encodes (float64Mul v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w64 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.mul_float64 v1 v2)
    (float64Encodes_exists _)

theorem wp_float64_div {t : go.GoType} [t ↓u go.float64] (v1 v2 : w64) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoDiv t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w64), RET #f; ⌜float64Encodes (float64Div v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w64 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.div_float64 v1 v2)
    (float64Encodes_exists _)

theorem wp_float64_neg {t : go.GoType} [t ↓u go.float64] (v : w64) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoUnOp GoNeg t))) (Val #v)) @ s; E
    {{ (f : w64), RET #f; ⌜float64Encodes (float64Neg v) f⌝ }} :=
  wp_go_step_rel (fun f : w64 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.neg_float64 v)
    (float64Encodes_exists _)

theorem wp_float32_add {t : go.GoType} [t ↓u go.float32] (v1 v2 : w32) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoPlus t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w32), RET #f; ⌜float32Encodes (float32Add v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w32 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.plus_float32 v1 v2)
    (float32Encodes_exists _)

theorem wp_float32_sub {t : go.GoType} [t ↓u go.float32] (v1 v2 : w32) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoSub t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w32), RET #f; ⌜float32Encodes (float32Sub v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w32 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.sub_float32 v1 v2)
    (float32Encodes_exists _)

theorem wp_float32_mul {t : go.GoType} [t ↓u go.float32] (v1 v2 : w32) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoMul t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w32), RET #f; ⌜float32Encodes (float32Mul v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w32 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.mul_float32 v1 v2)
    (float32Encodes_exists _)

theorem wp_float32_div {t : go.GoType} [t ↓u go.float32] (v1 v2 : w32) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoDiv t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w32), RET #f; ⌜float32Encodes (float32Div v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w32 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.div_float32 v1 v2)
    (float32Encodes_exists _)

theorem wp_float32_neg {t : go.GoType} [t ↓u go.float32] (v : w32) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoUnOp GoNeg t))) (Val #v)) @ s; E
    {{ (f : w32), RET #f; ⌜float32Encodes (float32Neg v) f⌝ }} :=
  wp_go_step_rel (fun f : w32 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.neg_float32 v)
    (float32Encodes_exists _)

end wp

end Perennial
