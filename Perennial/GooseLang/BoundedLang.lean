/-
The step-bounded GooseLang semantics: the proof device behind time receipts
(Mével, Jourdan, Pottier, "Time credits and time receipts in Iris", ESOP 2019).

The real semantics (`base_step`, `gooseRealEctxiLang` in `Lang.lean`) is the
trusted model of Go and is unchanged. This file adds a separate layer on top of
it: the state of the registered iris-lean language `goose_ectxi_lang` is
`BcfgState = CfgState × Nat`, the real configuration together with a *fuel*
`f`, the number of counted steps that may still be taken. A base step of the
bounded language (`BoundedBaseStep`) is

* for an uncounted redex: a real base step, fuel unchanged;
* for a counted redex, with fuel `f + 1`: a real base step, fuel `f` (`tick`);
* for a counted redex that is (really) reducible, with fuel `0`: a *stutter*
  (expression and state unchanged, no observations, no forks).

The bound `N` of time receipts is not a parameter of the language: it is the
*initial* fuel plus one. The adequacy theorems (`Adequacy.lean`) start the
bounded semantics with fuel `N - 1` for an arbitrary `N > 0` chosen by the
client, and the receipt ghost state (`receiptGS`, `Receipts.lean`) records `N`
as `receiptBound`; the state interpretation ties the two together (fuel `f`
means `N - 1 - f` counted steps so far, `receiptFuel`). This is the paper's
"`tick` diverges at the limit": at most `N - 1` counted steps succeed, so `N`
time receipts are contradictory, while NotStuck WPs stay provable (a
stuttering step is a step). Every bounded step is backed by a real base step,
so bounded reducibility implies real reducibility, and a real execution of at
most `f` steps is also an execution of the bounded language started with fuel
`f` (simulation lemmas below).

**Which steps are counted.** The counted redexes are the Go instructions
`App (Val (GoInstruction op)) (Val v)` (function/method resolution, typed
loads/stores/allocations, struct operations, ...). This differs from the
paper, whose tick translation puts a `tick` in front of every operation: a
step that may stutter is neither pure (`PureExec` needs the same reduct in
every state) nor atomic (a stutter does not reach a value), and the program
logic relies on `PureExec` for the pure steps and on `Language.Atomic` for the
heap primitives (`Load`, `AtomicAdd`, `CmpXchg`, ...) around which invariants
and atomic updates are opened. Go instructions are neither: their lifting
lemma (`wp_GoInstruction`) is the only rule for them, so it can absorb the
stutter (by Löb induction) and hand out a receipt. Since every Go function call
and typed memory access goes through a Go instruction, receipts are plentiful;
the adequacy assumption (fewer than `N` steps in total) bounds the number of
counted steps a fortiori.
-/
import Perennial.GooseLang.Lang

noncomputable section

namespace Perennial

open Iris.ProgramLogic

section bounded
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]

/-- The state of the bounded language: the real configuration and the fuel, the
number of counted steps that may still be taken. -/
abbrev BcfgState := CfgState × Nat

/-- The counted redexes: Go instructions. -/
def isCounted : Expr → Bool
  | .App (.Val (.GoInstruction _)) (.Val _) => true
  | _ => false

/-- The base step of the bounded language (see the module docstring). -/
inductive BoundedBaseStep :
    Expr → BcfgState → List Observation → Expr → BcfgState → List Expr → Prop
  | step {e σ f κ e' σ' efs} :
      isCounted e = false → BaseStep e σ κ e' σ' efs →
      BoundedBaseStep e (σ, f) κ e' (σ', f) efs
  | tick {e σ f κ e' σ' efs} :
      isCounted e = true → BaseStep e σ κ e' σ' efs →
      BoundedBaseStep e (σ, f + 1) κ e' (σ', f) efs
  | stutter {e σ κ e' σ' efs} :
      isCounted e = true → BaseStep e σ κ e' σ' efs →
      BoundedBaseStep e (σ, 0) [] e (σ, 0) []

theorem BoundedBaseStep.real {e s κ e' s' efs} (h : BoundedBaseStep e s κ e' s' efs) :
    ∃ κ' e'' σ'' efs', BaseStep e s.1 κ' e'' σ'' efs' := by
  cases h with
  | step _ h => exact ⟨_, _, _, _, h⟩
  | tick _ h => exact ⟨_, _, _, _, h⟩
  | stutter _ h => exact ⟨_, _, _, _, h⟩

/-- For an uncounted redex, bounded and real base steps agree. -/
theorem boundedBaseStep_uncounted {e σ f κ e' s' efs} (hnc : isCounted e = false) :
    BoundedBaseStep e (σ, f) κ e' s' efs ↔ ∃ σ', s' = (σ', f) ∧ BaseStep e σ κ e' σ' efs := by
  constructor
  · intro h
    cases h with
    | step _ h => exact ⟨_, rfl, h⟩
    | tick h => rw [hnc] at h; cases h
    | stutter h => rw [hnc] at h; cases h
  · rintro ⟨σ', rfl, h⟩
    exact .step hnc h

/-- The registered iris-lean language instance of GooseLang: the bounded layer
over `base_step`. -/
instance goose_ectxi_lang : EctxItemLanguage Expr EctxItem BcfgState Observation val where
  toVal := toVal
  ofVal := Val
  coe_of_toVal_eq_some := of_to_val
  toVal_coe _ := rfl
  baseStep := fun (e, σ) κ (e', σ', efs) => BoundedBaseStep e σ κ e' σ' efs
  fillItem := fillItem
  fillItem_inj {Ki} := fillItem_inj Ki
  fillItem_val e Ki := fillItem_val Ki e
  fillItem_no_val_inj Ki1 Ki2 := fillItem_no_val_inj Ki1 Ki2
  val_stuck h := by
    obtain ⟨_, _, _, _, h⟩ := BoundedBaseStep.real h
    exact val_base_stuck h
  base_ctx_step_val {Ki} _ _ _ _ _ _ h := by
    obtain ⟨_, _, _, _, h⟩ := BoundedBaseStep.real h
    exact base_ctx_step_val Ki h

end bounded

/-! ## The real semantics and the simulation

The real GooseLang language (thread-pool steps, reducibility) is the one that
iris-lean's generic constructions (`EctxItemLanguage → EctxLanguage →
Language`) derive from the trusted `gooseRealEctxiLang`; it is passed
explicitly since the registered instance is the bounded one. -/

section real
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]

open Language.Notation EctxLanguage.Notation

/-- The real (unbounded) GooseLang language. -/
abbrev gooseRealLang : Language Expr CfgState Observation val :=
  @EctxLanguage.instLanguage _ _ _ _ _
    (@EctxItemLanguage.instEctxLanguage _ _ _ _ _ gooseRealEctxiLang)

/-- A real primitive (thread) step: a `base_step` in an evaluation context. -/
def RealPrimStep (e : Expr) (σ : CfgState) (κ : List Observation) (e' : Expr)
    (σ' : CfgState) (efs : List Expr) : Prop :=
  @PrimStep.primStep _ _ _ gooseRealLang.toPrimStep (e, σ) κ (e', σ', efs)

/-- `n` steps of the real thread-pool semantics. -/
def RealNsteps (n : Nat) (ρ₁ : List Expr × CfgState) (κs : List Observation)
    (ρ₂ : List Expr × CfgState) : Prop :=
  @Language.NSteps _ _ _ _ gooseRealLang n ρ₁ κs ρ₂

/-- A thread is not stuck in the real semantics: it is a value or it can take a
real primitive step. -/
def RealNotStuck (e : Expr) (σ : CfgState) : Prop :=
  (toVal e).isSome ∨ ∃ κ e' σ' efs, RealPrimStep e σ κ e' σ' efs

/-- A real thread-pool step from a state with fuel `f > 0` is also a step of the
bounded semantics, which leaves at least `f - 1` fuel. -/
theorem bounded_step_of_real {ρ₁ ρ₂ : List Expr × CfgState} {κ : List Observation} (f : Nat)
    (h : @Language.Step _ _ _ _ gooseRealLang ρ₁ κ ρ₂) (hf : 0 < f) :
    ∃ f', f ≤ f' + 1 ∧ Language.Step (ρ₁.1, ((ρ₁.2, f) : BcfgState)) κ (ρ₂.1, (ρ₂.2, f')) := by
  obtain ⟨H, t₁, t₂⟩ := h
  rename_i e σ e' σ' eₜ
  obtain ⟨hb⟩ := H
  rename_i e₁ e₂ K
  cases hk : isCounted e₁
  · exact ⟨f, by omega, Language.Step.atomic
      (BaseStep.ContextStep.intro (K := K) (BoundedBaseStep.step (f := f) hk hb)) t₁ t₂⟩
  · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    exact ⟨f', by omega, Language.Step.atomic
      (BaseStep.ContextStep.intro (K := K) (BoundedBaseStep.tick hk hb)) t₁ t₂⟩

/-- Simulation: a real execution of `n` steps is also an execution of the bounded
semantics started with any fuel `f ≥ n`. -/
theorem bounded_nsteps_of_real {n : Nat} {ρ₁ ρ₂ : List Expr × CfgState} {κs : List Observation}
    (h : RealNsteps n ρ₁ κs ρ₂) (f : Nat) (hf : n ≤ f) :
    ∃ f', Language.NSteps n (ρ₁.1, ((ρ₁.2, f) : BcfgState)) κs (ρ₂.1, (ρ₂.2, f')) := by
  unfold RealNsteps at h
  induction h generalizing f with
  | refl ρ => exact ⟨f, .refl _⟩
  | cons hstep _ ih =>
    obtain ⟨f₁, hf₁, hstep'⟩ := bounded_step_of_real f hstep (by omega)
    obtain ⟨f', hsteps'⟩ := ih f₁ (by omega)
    exact ⟨f', .cons hstep' hsteps'⟩

/-- Bounded reducibility implies real reducibility: every bounded step is backed
by a real base step. -/
theorem realNotStuck_of_bounded {e : Expr} {σ : CfgState} {f : Nat}
    (h : PrimStep.NotStuck (e, ((σ, f) : BcfgState))) : RealNotStuck e σ := by
  rcases h with h | ⟨κ, e', s', efs, H⟩
  · exact .inl h
  · right
    obtain ⟨hb⟩ := H
    rename_i e₁ e₂ K
    obtain ⟨κ', e'', σ'', efs', hr⟩ := BoundedBaseStep.real hb
    exact ⟨κ', _, σ'', efs', letI := gooseRealEctxiLang; BaseStep.ContextStep.intro (K := K) hr⟩

end real

end Perennial
