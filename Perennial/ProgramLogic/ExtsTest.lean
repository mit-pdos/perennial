/-
Composing GooseLang extensions (regression test).

A toy extension, `tickExt` (a per-node counter: `tick` returns the counter and
increments it), is defined, given a semantics and a ghost state, and specified
for any program whose extensions include it (`HasExt tickExt`), exactly as the
Grove extension is. A program can use both: the closed list `[groveExt,
tickExt]` (`groveTickExts`) gets the specs of both extensions, each through its
own `HasExt` instance, and its adequacy obligations are those of both.
-/
module

public import Perennial.GooseLang.Adequacy
public import Perennial.GooseLang.Ext.Grove.Specs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace ExtsTest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## A toy extension -/

inductive TickOp where
  | tick

instance : Pos.Countable TickOp :=
  .ofInjective (fun _ => Pos.Countable.encode (0 : Nat)) (by intro a b _; cases a; cases b; rfl)

/-- A per-node counter. -/
@[reducible] def tickExt : GooseExt where
  Op := TickOp
  Val := Empty
  LocalState := Nat
  GlobalState := Unit

section step
variable [GooseExts] [ElemExt tickExt] [GoGlobalContext]

inductive TickStep : TickOp → val → GMap Loc (NonAtomic val) → Nat → Unit → Expr →
    GMap Loc (NonAtomic val) → Nat → Unit → Prop
  | tick (h : GMap Loc (NonAtomic val)) (n : Nat) :
      TickStep .tick #() h n () (Val #(BitVec.ofNat 64 n)) h (n + 1) ()

end step

instance tick_semantics : ExtSemantics tickExt where
  step := TickStep

instance tick_interp : ExtInterp tickExt where
  LocalGS _ := Unit
  GlobalGS _ := Unit
  localCtx _ _ := iprop(True)
  globalCtx _ _ := iprop(True)
  PreG _ := Unit
  initgP _ := True
  initP _ _ := True
  globalStart _ _ := iprop(True)
  localStart _ _ := iprop(True)
  global_init _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial
  local_init _ _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial

/-! ## Its spec, for any program that includes it -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tickExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

theorem wp_tick :
    {{ (True : IProp GF) }} (ExternalOp (extOp tickExt .tick) (Val #())) @ s; E
    {{ (n : w64), RET #n; True }} := by
  iintro %Φ _ HΦ
  iapply wp_extStep TickOp.tick #() Φ (by simp)
  iintro %h %n %g Hh Hl Hg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact ⟨_, h, n + 1, (), TickStep.tick h n⟩
  inext
  iintro %e' %h' %n' %g' %Hst _
  cases (show TickStep _ _ _ _ _ _ _ _ _ from Hst)
  imod Hclose
  imodintro
  iframe Hh Hl Hg
  iapply wp_value'
  iapply HΦ
  itrivial

end spec

/-! ## A program with both Grove and the counter -/

@[reducible] def groveTickExts : GooseExts := ⟨[groveExt, tickExt]⟩

attribute [local instance] groveTickExts

@[reducible] def groveTickSemantics : GooseSemantics := ⟨(grove_semantics, tick_semantics, ⟨⟩)⟩

@[reducible] def groveTickInterp : GooseInterp := ⟨(grove_interp, tick_interp, ⟨⟩)⟩

attribute [local instance] groveTickSemantics groveTickInterp

@[reducible] def groveTick_hasGrove : HasExt groveExt where
  mem := .here
  sem_eq := rfl
  interp_eq := rfl

@[reducible] def groveTick_hasTick : HasExt tickExt where
  mem := .there .here
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] groveTick_hasGrove groveTick_hasTick

section closed
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

-- the specs of both extensions apply to the program
example : {{ (True : IProp GF) }} (ExternalOp (extOp tickExt .tick) (Val #())) @ s; E
    {{ (n : w64), RET #n; True }} := wp_tick

example (t : Nat) : {{ tscLb (L := L) t }} (ExternalOp (extOp groveExt GroveOp.GetTscOp) (Val (#()))) @ s; E
    {{ (t' : w64), RET #t'; ⌜t ≤ t'.toNat⌝ ∗ tscLb t'.toNat }} := wp_GetTscOp t

-- the operations of the two extensions are distinct operations of the program
example : extOp groveExt GroveOp.GetTscOp ≠ extOp tickExt TickOp.tick := by
  intro h; cases h

-- an operation of one extension cannot change the other's state
example (σg σg' : CfgState) (v : val) (e' : Expr)
    (h : extStep (extOp tickExt TickOp.tick) v σg e' σg') :
    extGlobal groveExt σg'.2.globalWorld = extGlobal groveExt σg.2.globalWorld ∧
      extLocal groveExt σg'.1.world = extLocal groveExt σg.1.world := by
  obtain ⟨_, _, _, _, rfl⟩ := (extStep_injOp _ _ _ _ _ _).1 h
  exact ⟨rfl, rfl⟩

-- adequacy's conditions on the initial state are those of both extensions
example (g : GlobalState) (σ : state) :
    extsInitgP g.globalWorld ∧ extsInitP σ.world g.globalWorld :=
  ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩⟩

end closed

end ExtsTest

end Perennial
