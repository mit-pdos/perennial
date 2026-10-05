import Iris
import Perennial.Std.GMap
import Perennial.Algebra.TimeReceipt

/-!
Port of `new/ghost/all.v`: a universal camera and an `own` that needs no
per-algebra `inG` assumption.

# Design (read this before writing ghost-state proofs)

Rocq: a single `allG Σ` provides `inG Σ (allUR (iPropO Σ))` where
`allUR = discrete_funUR (optionUR ∘ int_cmra)` is a product over a *syntax* of
camera codes (`syntax.cmra`). `own γ (a : A)` requires `IsCmra (iProp Σ) A e`
(evidence `A = int_cmra e`) and owns the singleton `{[e := Some a]}`.

Lean (this file), built on iris-lean's `BundledGFunctors`/`ElemG`/`iOwn`:

* `Syntax.ty`, `Syntax.ofe`, `Syntax.cmra`, `Syntax.ucmra` are codes. They live
  in `Type` (universe 0) and therefore cannot mention arbitrary types:
  iris-lean's invariants, later credits and gen_heap force `IProp GF : Type`,
  so a coproduct indexed by `Type` (as in Rocq, which uses universe
  polymorphism) is impossible. Leibniz data is coded by the small universe
  `Syntax.ty` (`Unit`, `Bool`, `Nat`, `Int`, `Pos`, `×`, `⊕`, `Option`, `List`).
  The ghost libraries (`ghost_var`, `ghost_map`, `mono_list`, `saved_pred`, ...)
  are generic over any type with `[Pos.Countable A]`: they store
  `Pos.Countable.encode a : Pos` (an injection) in the coded algebra.
* `intO`, `intF`, `intUF` interpret codes as (contractive) functors;
  `allURF := DiscreteFunOF (fun e => OptionOF (intF e).1)` is the universal
  functor.
* `class allG (GF : outParam BundledGFunctors)` bundles a single
  `ElemG GF allURF` (field `any_inG`). `GF` is an `outParam`, so in a context
  `[allG GF]` a bare `own γ a` (or `ghost_var γ q v`) elaborates with that
  `GF`. There should be exactly one `allG` instance in scope.
  Note: `allG` is defined for `GF : BundledGFunctors.{0,0,0}` (forced by the
  universe of the codes); downstream simply writes `{GF} [allG GF]`.
* `IsCmra PROP A e` (resp. `IsOfe`, `IsUcmra`, `IsTy`) is the evidence that the
  CMRA `A` *with its instance* is the denotation of the code `e` at `PROP`
  (an equation of bundled `Σ T, CMRA T`). Instances are found by type-class
  search, compositionally (`is_prodR`, `is_authR`, `is_gmap_viewR`, ...); `e`
  is an `outParam`. Codes must be syntax-directed on the (reducible) head of
  `A`, so that each type has exactly one code: e.g. `DFracAgreeR A = DFrac × Agree A`
  is coded by `prodR dfracR (agreeR _)` and `MonoNat = Auth MaxNat` by
  `authR max_natUR`. To support a new algebra, add a constructor to the codes,
  a case to `intF`/`intUF`, and an `is_*` instance.
* `own γ (a : A) [IsCmra (IProp GF) A e] : IProp GF :=
     iOwn (F := allURF) γ (discreteFunSingleton e (some a'))`
  where `a'` is `a` cast along the evidence. The core rules (`own_op`,
  `own_valid`, `own_updateP`, `own_alloc_strong_dep`, `own_unit`, `later_own`,
  `own_forall`, `own_timeless`, `own_core_persistent`) are proved here by
  substituting the evidence (tactic `own_start`) and reusing iris-lean's
  `iOwn` lemmas; derived rules are in `Perennial/Ghost/Own.lean`.
* Building a model: `«allΣ»` puts `allURF` at slot 0, with `«allG_allΣ»`;
  `allG_of_slot` builds `allG GF` for any `GF` that has `allURF` at some slot
  (Rocq `subG_allΣ`).

How a proof obtains ghost state: assume `{GF} [allG GF]` (or a GS class that
extends `allG GF`), then use `own`/the libraries directly, e.g.
`iMod (ghost_var_alloc v)`; no further class assumptions are needed, except
`[Pos.Countable A]` for the types of stored data.
-/

noncomputable section

namespace Perennial
open Iris COFE

namespace Syntax

/-- Codes for (small) Leibniz base types. -/
inductive ty where
  | unit | bool | nat | int | pos
  | prod (a b : ty) | sum (a b : ty) | option (a : ty) | list (a : ty)

/-- Codes for OFEs. -/
inductive ofe where
  | unitO
  | leibnizO (t : ty)
  | laterO
  | discrete_funO (t : ty) (o : ofe)
  | prodO (a b : ofe)

mutual
inductive cmra where
  | authR (A : ucmra)
  | gmap_viewR (K : ty) (V : cmra)
  | agreeR (A : ofe)
  | exclR (A : ofe)
  | mono_listR (A : ofe)
  | prodR (A B : cmra)
  | optionR (A : cmra)
  | csumR (A B : cmra)
  | natR
  | max_natR
  | fracR
  | dfracR
  /-- Rocq `positiveR`: positive naturals under addition (`Perennial.positive`). -/
  | positiveR
  /-- The time-receipt camera `TRView` (`Perennial/Algebra/TimeReceipt.lean`). -/
  | receiptR
inductive ucmra where
  | unitUR
  | natUR
  | max_natUR
  | prodUR (A B : ucmra)
  | optionUR (A : cmra)
  | gmapUR (K : ty) (V : cmra)
end

end Syntax

namespace Syntax.ty
def El : ty → Type
  | .unit => Unit | .bool => Bool | .nat => Nat | .int => Int | .pos => Pos
  | .prod a b => a.El × b.El | .sum a b => a.El ⊕ b.El
  | .option a => Option a.El | .list a => List a.El

instance decEq : (t : ty) → DecidableEq t.El
  | .unit => inferInstanceAs (DecidableEq Unit)
  | .bool => inferInstanceAs (DecidableEq Bool)
  | .nat => inferInstanceAs (DecidableEq Nat)
  | .int => inferInstanceAs (DecidableEq Int)
  | .pos => inferInstanceAs (DecidableEq Pos)
  | .prod a b => letI := decEq a; letI := decEq b; inferInstanceAs (DecidableEq (a.El × b.El))
  | .sum a b => letI := decEq a; letI := decEq b; inferInstanceAs (DecidableEq (a.El ⊕ b.El))
  | .option a => letI := decEq a; inferInstanceAs (DecidableEq (Option a.El))
  | .list a => letI := decEq a; inferInstanceAs (DecidableEq (List a.El))
end Syntax.ty

abbrev OFunctorB := Σ F : OFunctorPre.{0,0,0}, OFunctorContractive F
abbrev RFunctorB := Σ F : OFunctorPre.{0,0,0}, RFunctorContractive F
abbrev URFunctorB := Σ F : OFunctorPre.{0,0,0}, URFunctorContractive F

/-! ## Positive naturals under addition (Rocq `positiveR`) -/

/-- Rocq `positive` as a CMRA: `⟨k⟩` stands for `k + 1`, the operation is addition, and there
is no core. (Iris' `Pos` is binary and lacks the arithmetic lemmas needed here.) -/
@[ext] structure positive where
  ofPred ::
  pred : Nat
  deriving DecidableEq

namespace positive
instance : Add positive := ⟨fun x y => ⟨x.pred + y.pred + 1⟩⟩
@[simp] theorem add_pred (x y : positive) : (x + y).pred = x.pred + y.pred + 1 := rfl
/-- Rocq `Pos.of_nat` (with `of_nat 0 = 1`). -/
def of_nat (n : Nat) : positive := ⟨n - 1⟩
/-- `1%positive`. -/
def one : positive := ⟨0⟩
instance : Std.Associative (α := positive) (· + ·) := ⟨fun _ _ _ => by ext; simp; omega⟩
instance : Std.Commutative (α := positive) (· + ·) := ⟨fun _ _ => by ext; simp; omega⟩
instance : COFE positive := COFE.ofDiscrete positive
instance : OFE.Discrete positive := ⟨id⟩
instance : CMRA positive := PosCommMonoidLike.instCMRA
instance : CMRA.Discrete positive := PosCommMonoidLike.instDiscrete
end positive

def intO : Syntax.ofe → OFunctorB
  | .unitO => ⟨constOF Unit, inferInstance⟩
  | .leibnizO t => ⟨constOF (DiscreteO t.El), inferInstance⟩
  | .laterO => ⟨LaterOF IdOF, inferInstance⟩
  | .discrete_funO t o =>
    letI := (intO o).2
    ⟨DiscreteFunOF (fun _ : t.El => (intO o).1), inferInstance⟩
  | .prodO a b =>
    letI := (intO a).2; letI := (intO b).2
    ⟨ProdOF (intO a).1 (intO b).1, inferInstance⟩

instance (o : Syntax.ofe) : OFunctorContractive (intO o).1 := (intO o).2

mutual
def intF : Syntax.cmra → RFunctorB
  | .authR A => letI := (intUF A).2; ⟨Auth.AuthRF (intUF A).1, inferInstance⟩
  | .gmap_viewR K V =>
    letI := (intF V).2; letI := K.decEq
    ⟨HeapView.HeapViewURF (K := K.El) (H := gmap K.El) (intF V).1, inferInstance⟩
  | .agreeR A => ⟨AgreeRF (intO A).1, inferInstance⟩
  | .exclR A => ⟨Excl.ExclOF (intO A).1, inferInstance⟩
  | .mono_listR A => ⟨MonoListRF (intO A).1, inferInstance⟩
  | .prodR A B => letI := (intF A).2; letI := (intF B).2; ⟨ProdOF (intF A).1 (intF B).1, inferInstance⟩
  | .optionR A => letI := (intF A).2; ⟨OptionOF (intF A).1, inferInstance⟩
  | .csumR A B => letI := (intF A).2; letI := (intF B).2; ⟨Csum.OF (intF A).1 (intF B).1, inferInstance⟩
  | .natR => ⟨constOF Nat, inferInstance⟩
  | .max_natR => ⟨constOF MaxNat, inferInstance⟩
  | .fracR => ⟨constOF Qp, inferInstance⟩
  | .dfracR => ⟨constOF DFrac, inferInstance⟩
  | .positiveR => ⟨constOF positive, inferInstance⟩
  | .receiptR => ⟨constOF TRView, inferInstance⟩
def intUF : Syntax.ucmra → URFunctorB
  | .unitUR => ⟨constOF Unit, inferInstance⟩
  | .natUR => ⟨constOF Nat, inferInstance⟩
  | .max_natUR => ⟨constOF MaxNat, inferInstance⟩
  | .prodUR A B => letI := (intUF A).2; letI := (intUF B).2; ⟨ProdOF (intUF A).1 (intUF B).1, inferInstance⟩
  | .optionUR A => letI := (intF A).2; ⟨OptionOF (intF A).1, inferInstance⟩
  | .gmapUR K V =>
    letI := (intF V).2; letI := K.decEq
    ⟨PartialMap.PartialMapOF (gmap K.El) (intF V).1, inferInstance⟩
end

/-! ## The universal functor and `allG` -/

instance : DecidableEq Syntax.cmra := fun _ _ => Classical.propDecidable _

instance (e : Syntax.cmra) : RFunctorContractive (intF e).1 := (intF e).2
instance (e : Syntax.ucmra) : URFunctorContractive (intUF e).1 := (intUF e).2

/-- The universal functor: `∏ e, option (intF e)`, i.e. Rocq's
`discrete_funURF (λ A, optionURF (intF_cmra A))`. -/
abbrev allURF : OFunctorPre := DiscreteFunOF (fun e : Syntax.cmra => OptionOF (intF e).1)

/-- One `ElemG` for the universal functor gives ghost state of every algebra
with a code. -/
class allG (GF : outParam BundledGFunctors) where
  any_inG : ElemG GF allURF

attribute [reducible, instance] allG.any_inG

/-- A `BundledGFunctors` with the universal functor at slot 0 (Rocq `allΣ`). -/
def «allΣ» : BundledGFunctors := BundledGFunctors.default.set 0 ⟨allURF, inferInstance⟩

/-- Rocq `subG_allΣ`: any `GF` that contains `allURF` at some slot. -/
@[instance_reducible] def allG_of_slot {GF : BundledGFunctors} (τ : GType) (h : GF τ = ⟨allURF, inferInstance⟩) :
    allG GF := ⟨⟨τ, h⟩⟩

theorem «allΣ_slot» : «allΣ» 0 = ⟨allURF, inferInstance⟩ :=
  (by simp [«allΣ», BundledGFunctors.set])

@[instance_reducible] def «allG_allΣ» : allG «allΣ» := allG_of_slot 0 «allΣ_slot»

/-! ## Evidence that a CMRA has a code -/

/-- `IsTy A t`: the type `A` is denoted by the code `t`. -/
class IsTy (A : Type) (t : outParam Syntax.ty) : Prop where
  eq_ty : A = t.El

instance : IsTy Unit .unit := ⟨rfl⟩
instance : IsTy Bool .bool := ⟨rfl⟩
instance : IsTy Nat .nat := ⟨rfl⟩
instance : IsTy Int .int := ⟨rfl⟩
instance : IsTy Pos .pos := ⟨rfl⟩
instance [h1 : IsTy A a] [h2 : IsTy B b] : IsTy (A × B) (.prod a b) := by
  obtain ⟨rfl⟩ := h1; obtain ⟨rfl⟩ := h2; exact ⟨rfl⟩
instance [h1 : IsTy A a] [h2 : IsTy B b] : IsTy (A ⊕ B) (.sum a b) := by
  obtain ⟨rfl⟩ := h1; obtain ⟨rfl⟩ := h2; exact ⟨rfl⟩
instance [h1 : IsTy A a] : IsTy (Option A) (.option a) := by
  obtain ⟨rfl⟩ := h1; exact ⟨rfl⟩
instance [h1 : IsTy A a] : IsTy (List A) (.list a) := by
  obtain ⟨rfl⟩ := h1; exact ⟨rfl⟩

section denote
variable (PROP : Type) [COFE PROP]

/-- Rocq `IsOfe`: `A` (with its OFE structure) is the denotation of `e` at `PROP`. -/
class IsOfe (A : Type) [OFE A] (e : outParam Syntax.ofe) : Prop where
  eq_ofe : (⟨A, inferInstance⟩ : Σ T : Type, OFE T) = ⟨(intO e).1 PROP PROP, inferInstance⟩

/-- Rocq `IsCmra`: `A` (with its CMRA structure) is the denotation of `e` at `PROP`. -/
class IsCmra (A : Type) [CMRA A] (e : outParam Syntax.cmra) : Prop where
  eq_cmra : (⟨A, inferInstance⟩ : Σ T : Type, CMRA T) = ⟨(intF e).1 PROP PROP, inferInstance⟩

/-- Rocq `IsUcmra`. -/
class IsUcmra (A : Type) [UCMRA A] (e : outParam Syntax.ucmra) : Prop where
  eq_ucmra : (⟨A, inferInstance⟩ : Σ T : Type, UCMRA T) = ⟨(intUF e).1 PROP PROP, inferInstance⟩

end denote

/-- Destruct an `IsOfe`/`IsCmra`/`IsUcmra`/`IsTy` hypothesis, substituting the type
(and its structure) by the denotation. -/
syntax "is_subst " ident : tactic
macro_rules
  | `(tactic| is_subst $h) => `(tactic|
      (obtain ⟨h'⟩ := $h:ident; have ⟨e1, e2⟩ := Sigma.mk.inj h'; subst e1
       have e3 := eq_of_heq e2; subst e3; clear h'))




section instances
variable {PROP : Type} [COFE PROP]

instance is_unitO : IsOfe PROP Unit .unitO := ⟨rfl⟩
instance is_leibnizO [h : IsTy A t] : IsOfe PROP (DiscreteO A) (.leibnizO t) := by
  obtain ⟨rfl⟩ := h; exact ⟨rfl⟩
instance is_laterO : IsOfe PROP (Later PROP) .laterO := ⟨rfl⟩
instance is_discrete_funO [ht : IsTy A t] [OFE B] [hB : IsOfe PROP B o] :
    IsOfe PROP (A → B) (.discrete_funO t o) := by
  obtain ⟨rfl⟩ := ht; is_subst hB; exact ⟨rfl⟩
instance is_prodO [OFE A] [OFE B] [hA : IsOfe PROP A a] [hB : IsOfe PROP B b] :
    IsOfe PROP (A × B) (.prodO a b) := by
  is_subst hA; is_subst hB; exact ⟨rfl⟩

instance is_authR [UCMRA A] [hA : IsUcmra PROP A a] : IsCmra PROP (Auth A) (.authR a) := by
  is_subst hA; exact ⟨rfl⟩
instance is_gmap_viewR [hK : IsTy K k] [dK : DecidableEq K] [CMRA V] [hV : IsCmra PROP V v] :
    IsCmra PROP (HeapView K V (gmap K)) (.gmap_viewR k v) := by
  obtain ⟨rfl⟩ := hK; obtain rfl : dK = k.decEq := Subsingleton.elim _ _
  is_subst hV; exact ⟨rfl⟩
instance is_agreeR [OFE A] [hA : IsOfe PROP A a] : IsCmra PROP (Agree A) (.agreeR a) := by
  is_subst hA; exact ⟨rfl⟩
instance is_exclR [OFE A] [hA : IsOfe PROP A a] : IsCmra PROP (Excl A) (.exclR a) := by
  is_subst hA; exact ⟨rfl⟩
instance is_mono_listR [OFE A] [hA : IsOfe PROP A a] : IsCmra PROP (MonoList A) (.mono_listR a) := by
  is_subst hA; exact ⟨rfl⟩
instance is_prodR [CMRA A] [CMRA B] [hA : IsCmra PROP A a] [hB : IsCmra PROP B b] :
    IsCmra PROP (A × B) (.prodR a b) := by
  is_subst hA; is_subst hB; exact ⟨rfl⟩
instance is_optionR [CMRA A] [hA : IsCmra PROP A a] : IsCmra PROP (Option A) (.optionR a) := by
  is_subst hA; exact ⟨rfl⟩
instance is_csumR [CMRA A] [CMRA B] [hA : IsCmra PROP A a] [hB : IsCmra PROP B b] :
    IsCmra PROP (Csum A B) (.csumR a b) := by
  is_subst hA; is_subst hB; exact ⟨rfl⟩
instance is_natR : IsCmra PROP Nat .natR := ⟨rfl⟩
instance is_max_natR : IsCmra PROP MaxNat .max_natR := ⟨rfl⟩
instance is_fracR : IsCmra PROP Qp .fracR := ⟨rfl⟩
instance is_dfracR : IsCmra PROP DFrac .dfracR := ⟨rfl⟩
instance is_positiveR : IsCmra PROP positive .positiveR := ⟨rfl⟩
instance is_receiptR : IsCmra PROP TRView .receiptR := ⟨rfl⟩

instance is_unitUR : IsUcmra PROP Unit .unitUR := ⟨rfl⟩
instance is_natUR : IsUcmra PROP Nat .natUR := ⟨rfl⟩
instance is_max_natUR : IsUcmra PROP MaxNat .max_natUR := ⟨rfl⟩
instance is_prodUR [UCMRA A] [UCMRA B] [hA : IsUcmra PROP A a] [hB : IsUcmra PROP B b] :
    IsUcmra PROP (A × B) (.prodUR a b) := by
  is_subst hA; is_subst hB; exact ⟨rfl⟩
instance is_optionUR [CMRA A] [hA : IsCmra PROP A a] : IsUcmra PROP (Option A) (.optionUR a) := by
  is_subst hA; exact ⟨rfl⟩
instance is_gmapUR [hK : IsTy K k] [dK : DecidableEq K] [CMRA V] [hV : IsCmra PROP V v] :
    IsUcmra PROP (gmap K V) (.gmapUR k v) := by
  obtain ⟨rfl⟩ := hK; obtain rfl : dK = k.decEq := Subsingleton.elim _ _
  is_subst hV; exact ⟨rfl⟩

end instances

/-! ## Ownership -/

section own
open BI OFE CMRA

variable {GF : BundledGFunctors} [allG GF]

/-- Transport an element along `IsCmra`. -/
def IsCmra.to {PROP : Type} [COFE PROP] {A : Type} [CMRA A] {e : Syntax.cmra}
    (H : IsCmra PROP A e) (a : A) : (intF e).1 PROP PROP :=
  cast (congrArg Sigma.fst H.eq_cmra) a

/-- Rocq `own`: ownership of `a : A` at ghost name `γ`, for any `A` with a code. -/
def own {A : Type} [CMRA A] {e : outParam Syntax.cmra} [H : IsCmra (IProp GF) A e]
    (γ : GName) (a : A) : IProp GF :=
  iOwn (F := allURF) γ (discreteFunSingleton e (some (H.to a)))

/-- Unfold `own` to `iOwn` of a singleton, after substituting `A` by its denotation. -/
syntax "own_start " ident : tactic
macro_rules
  | `(tactic| own_start $H) => `(tactic|
      (obtain ⟨h'⟩ := $H:ident; have ⟨e1, e2⟩ := Sigma.mk.inj h'; subst e1
       have e3 := eq_of_heq e2; subst e3
       unfold own IsCmra.to; simp only [cast_eq]))

variable {A : Type} [CMRA A] {e : Syntax.cmra} [H : IsCmra (IProp GF) A e]

private theorem own_unfold (γ : GName) (a : A) :
    own γ a = iOwn (F := allURF) γ (discreteFunSingleton e (some (H.to a))) := rfl

/-- `IsCmra.to` is a CMRA isomorphism (it is a cast). -/
theorem IsCmra.to_op (a b : A) : H.to (a • b) = H.to a • H.to b := by
  obtain ⟨h'⟩ := H; have ⟨e1, e2⟩ := Sigma.mk.inj h'; subst e1
  have e3 := eq_of_heq e2; subst e3; rfl
theorem IsCmra.to_validN {n} (a : A) : ✓{n} H.to a ↔ ✓{n} a := by
  obtain ⟨h'⟩ := H; have ⟨e1, e2⟩ := Sigma.mk.inj h'; subst e1
  have e3 := eq_of_heq e2; subst e3; rfl
theorem IsCmra.to_valid (a : A) : ✓ H.to a ↔ ✓ a := by
  obtain ⟨h'⟩ := H; have ⟨e1, e2⟩ := Sigma.mk.inj h'; subst e1
  have e3 := eq_of_heq e2; subst e3; rfl

/-- The inverse of `IsCmra.to`. -/
def IsCmra.of (H : IsCmra (IProp GF) A e) (c : (intF e).1 (IProp GF) (IProp GF)) : A :=
  cast (congrArg Sigma.fst H.eq_cmra).symm c

theorem IsCmra.to_of (c : (intF e).1 (IProp GF) (IProp GF)) : H.to (H.of c) = c := by
  simp [IsCmra.to, IsCmra.of]
theorem IsCmra.of_to (a : A) : H.of (H.to a) = a := by
  simp [IsCmra.to, IsCmra.of]

instance own_ne (γ : GName) : NonExpansive (own (A := A) (GF := GF) γ) := by
  own_start H
  exact ⟨fun _ _ _ h => iOwn_ne.ne (NonExpansive.ne (some_dist_some.mpr h))⟩

theorem own_op (γ : GName) (a1 a2 : A) : own γ (a1 • a2) ⊣⊢ own γ a1 ∗ own γ a2 := by
  own_start H
  rw [← iOwn_op.to_eq, discreteFunSingleton_op_eq]; exact .rfl

theorem own_valid (γ : GName) (a : A) : own γ a ⊢ ✓ a := by
  own_start H
  refine iOwn_cmraValid.trans ?_
  refine internalCmraValid_entails.mpr fun n h => ?_
  exact (discreteFunSingleton_validN_iff n _).mp h

instance own_timeless (γ : GName) (a : A) [DiscreteE a] : Timeless (own γ a) := by
  own_start H
  haveI : ∀ i, DiscreteE (UCMRA.unit : Option ((intF i).1 (IProp GF) (IProp GF))) :=
    fun _ => Option.none_is_discrete
  infer_instance

instance own_core_persistent (γ : GName) (a : A) [CoreId a] : Persistent (own γ a) := by
  own_start H; infer_instance

private theorem singleton_le_self (r : allURF.ap (IProp GF)) :
    discreteFunSingleton e (r e) ≼ r :=
  ⟨discreteFunInsert e UCMRA.unit r, (discreteFunSingleton_op_insert CMRA.unit_right_id).symm⟩

private instance eval_ne (e : Syntax.cmra) :
    NonExpansive (fun r : allURF.ap (IProp GF) => r e) := ⟨fun _ _ _ h => h e⟩

theorem later_own (γ : GName) (a : A) : ▷ own γ a ⊢ ◇ ∃ b, own γ b ∧ ▷ (a ≡ b) := by
  own_start H
  refine later_iOwn.trans ((except0_mono (exists_elim fun r => ?_)).trans except0_idem.1)
  have heq : ▷ (discreteFunSingleton e (some a) ≡ r) ⊢@{IProp GF} ▷ (some a ≡ r e) :=
    later_mono ((internalEq.of_internalEquiv_ne (fun r : allURF.ap (IProp GF) => r e)).trans
      (by rw [discreteFunSingleton_self]))
  match hrc : r e with
  | some c =>
    rw [hrc] at heq
    refine .trans ?_ except0_intro
    refine .trans ?_ (exists_intro c)
    refine and_mono ?_ (heq.trans (later_mono (option_some_equivI a c).1))
    exact iOwn_mono (hrc ▸ singleton_le_self r)
  | none =>
    rw [hrc] at heq
    exact and_elim_r.trans ((heq.trans (later_mono (option_some_none_equivI a).1)).trans or_intro_l)

private def evalO (e : Syntax.cmra) (o : Option (allURF.ap (IProp GF))) :
    Option ((intF e).1 (IProp GF) (IProp GF)) := o.bind (· e)

private instance evalO_ne (e : Syntax.cmra) : NonExpansive (evalO (GF := GF) e) where
  ne {n x y} h := by
    rcases x with _ | x <;> rcases y with _ | y
    · exact .rfl
    · exact h.elim
    · exact h.elim
    · exact h e

private theorem evalO_op (e : Syntax.cmra) (x y : Option (allURF.ap (IProp GF))) :
    evalO e (x • y) = evalO e x • evalO e y := by
  rcases x with _ | x <;> rcases y with _ | y
  · rfl
  · show y e = none • y e; generalize y e = t; cases t <;> rfl
  · show x e = x e • none; generalize x e = t; cases t <;> rfl
  · rfl

theorem own_forall {B : Type _} [Inhabited B] (γ : GName) (f : B → A) :
    (∀ b, own γ (f b)) ⊢ ∃ c, own γ c ∗ ∀ b, some (f b) ≼ some c := by
  own_start H
  refine (iOwn_forall (F := allURF) γ _).trans (exists_elim fun r => ?_)
  have hinc : ∀ b, some (discreteFunSingleton e (some (f b))) ≼ some r ⊢@{IProp GF}
      some (f b) ≼ r e := fun b => by
    have := internalCmraIncluded_map (PROP := IProp GF) (evalO e) (evalO_op e)
      (a := some (discreteFunSingleton e (some (f b)))) (b := some r)
    simpa [evalO, discreteFunSingleton_self] using this
  match hrc : r e with
  | some c =>
    refine .trans ?_ (exists_intro c)
    refine sep_mono (iOwn_mono (hrc ▸ singleton_le_self r)) (forall_mono fun b => ?_)
    exact (hinc b).trans (by rw [hrc])
  | none =>
    refine sep_elim_right.trans ((forall_elim default).trans ((hinc default).trans ?_))
    rw [hrc]
    refine (internalCmraIncluded_pure (φ := False) fun n => ⟨fun h => ?_, False.elim⟩).1.trans
      (pure_elim' False.elim)
    rcases Option.incN_iff.mp h with h | ⟨_, _, _, h, _⟩ <;> cases h

theorem own_updateP (P : A → Prop) (γ : GName) (a : A) (Hupd : a ~~>: P) :
    own γ a ⊢ |==> ∃ a', ⌜P a'⌝ ∗ own γ a' := by
  own_start H
  refine (iOwn_updateP (discreteFunSingleton_updateP' (UpdateP.option' _ _ Hupd))).trans ?_
  refine BIUpdate.mono (exists_elim fun x => ?_)
  iintro ⟨%hx, Hx⟩
  obtain ⟨y, rfl, hy⟩ := hx
  cases y with
  | none => exact hy.elim
  | some c =>
    iexists c
    isplitr
    · ipureintro; exact hy
    · iexact Hx

theorem own_alloc_strong_dep (f : GName → A) (P : GName → Prop) (HP : PredInfinite P)
    (Hf : ∀ γ, P γ → ✓ f γ) : ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ (f γ) := by
  own_start H
  exact iOwn_alloc_strong_dep (F := allURF) _ P HP.exists_ge fun γ hγ =>
    (discreteFunSingleton_valid_iff _).mpr (Hf γ hγ)

theorem own_unit {B : Type} [UCMRA B] {e : Syntax.cmra} [HB : IsCmra (IProp GF) B e]
    (γ : GName) : ⊢ |==> own γ (UCMRA.unit : B) := by
  have hupd : (UCMRA.unit : Option ((intF e).1 (IProp GF) (IProp GF))) ~~> some (HB.to UCMRA.unit) := by
    intro n mz hv
    match mz with
    | none | some none =>
      exact (HB.to_validN _).mpr UCMRA.unit_valid.validN
    | some (some c) =>
      show ✓{n} (HB.to UCMRA.unit • c)
      have hc : ✓{n} c := hv
      rw [show HB.to UCMRA.unit • c = HB.to (UCMRA.unit • HB.of c) by rw [HB.to_op, HB.to_of],
        UCMRA.unit_left_id, HB.to_of]; exact hc
  rw [own_unfold]
  exact (iOwn_unit (γ := γ) (ε := (UCMRA.unit : allURF.ap (IProp GF)))).trans
    ((bupd_mono (iOwn_update (discreteFunSingleton_update_unit hupd))).trans bupd_trans)

end own
end Perennial
