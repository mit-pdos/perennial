module

public import Iris
public import Perennial.Std.GMap

@[expose] public section

/-!
A universal camera and an `own` that needs no
per-algebra `inG` assumption.

# Design (read this before writing ghost-state proofs)

Idea: a single `AllG GF` provides one ghost-state slot for the universal camera
`∏ e, option (int e)`, a product over a *syntax* of camera codes. `own γ (a : A)`
requires `IsCmra (IProp GF) A e` (an isomorphism `A ≅ int e`) and owns the singleton
`{[e := some a]}`.

Built on iris-lean's `BundledGFunctors`/`ElemG`/`iOwn`:

* `Syntax.Ty`, `Syntax.Ofe`, `Syntax.Cmra`, `Syntax.Ucmra` are codes. They live
  in `Type` (universe 0) and therefore cannot mention arbitrary types: a
  coproduct indexed by all types would need a universe above `IProp GF`'s.
  Leibniz data is coded by the small universe
  `Syntax.Ty` (`Unit`, `Bool`, `Nat`, `Int`, `Pos`, `×`, `⊕`, `Option`, `List`).
  The ghost libraries (`ghost_var`, `ghost_map`, `mono_list`, `saved_pred`, ...)
  are generic over any type with `[Pos.Countable A]`: they store
  `Pos.Countable.encode a : Pos` (an injection) in the coded algebra.
* `intO`, `intF`, `intUF` interpret codes as (contractive) functors at any
  universe `w` (that of `IProp GF`, which is above the step-index type
  `Ordinal.{3}`: `IProp GF : Type (max u 4)`); the codes' Type-0 leaves are
  lifted with `ULift` (`constOFU`). `AllURF := DiscreteFunOF (fun e => OptionOF
  (intF e).1)` is the universal functor.
* `class AllG (GF : outParam BundledGFunctors)` bundles a single
  `ElemG GF AllURF` (field `any_inG`). `GF` is an `outParam`, so in a context
  `[AllG GF]` a bare `own γ a` (or `ghostVar γ q v`) elaborates with that
  `GF`. There should be exactly one `AllG` instance in scope.
* `IsCmra PROP A e` (resp. `IsOfe`, `IsUcmra`) is the evidence that the CMRA
  `A` *with its instance* is isomorphic to the denotation of the code `e` at
  `PROP` (`CmraIso`: CMRA homomorphisms both ways, mutually inverse; `IsUcmra`
  also preserves the unit); `IsTy A t` is the equation `A = t.El`. They are
  data, since the denotation lives in a higher universe than `A`. Instances are found by type-class
  search, compositionally (`is_prodR`, `is_authR`, `is_gmap_viewR`, ...); `e`
  is an `outParam`. Codes must be syntax-directed on the (reducible) head of
  `A`, so that each type has exactly one code: e.g. `DFracAgreeR A = DFrac × Agree A`
  is coded by `prodR dfracR (agreeR _)` and `MonoNat = Auth MaxNat` by
  `authR maxNatUR`. To support a new algebra, add a constructor to the codes,
  a case to `intF`/`intUF`, and an `is_*` instance.
* `own γ (a : A) [IsCmra (IProp GF) A e] : IProp GF :=
     iOwn (F := AllURF) γ (discreteFunSingleton e (some (H.iso.to a)))`.
  The core rules (`own_op`, `own_valid`, `own_updateP`, `own_alloc_strong_dep`,
  `own_unit`, `own_forall`, `own_timeless`, `own_core_persistent`, and
  `later_own` for finite step indices only) are proved here by transporting
  along the isomorphism and reusing iris-lean's `iOwn` lemmas; derived rules
  are in `Perennial/Ghost/Own.lean`.
* Building a model: `«allΣ»` puts `AllURF` at slot 0, with `«allG_allΣ»`;
  `allGOfSlot` builds `AllG GF` for any `GF` that has `AllURF` at some slot.

How a proof obtains ghost state: assume `{GF} [AllG GF]` (or a GS class that
extends `AllG GF`), then use `own`/the libraries directly, e.g.
`imod ghostVar_alloc v`; no further class assumptions are needed, except
`[Pos.Countable A]` for the types of stored data.
-/

noncomputable section

namespace Perennial
open Iris COFE

namespace Syntax

/-- Codes for (small) Leibniz base types. -/
inductive Ty where
  | unit | bool | nat | int | pos
  | prod (a b : Ty) | sum (a b : Ty) | option (a : Ty) | list (a : Ty)

/-- Codes for OFEs. -/
inductive Ofe where
  | unitO
  | leibnizO (t : Ty)
  | laterO
  | discreteFunO (t : Ty) (o : Ofe)
  | prodO (a b : Ofe)

mutual
inductive Cmra where
  | authR (A : Ucmra)
  | gmapViewR (K : Ty) (V : Cmra)
  | agreeR (A : Ofe)
  | exclR (A : Ofe)
  | monoListR (A : Ofe)
  | prodR (A B : Cmra)
  | optionR (A : Cmra)
  | csumR (A B : Cmra)
  | natR
  | maxNatR
  | fracR
  | dfracR
  /-- Positive naturals under addition (`Perennial.positive`). -/
  | positiveR
inductive Ucmra where
  | unitUR
  | natUR
  | maxNatUR
  | prodUR (A B : Ucmra)
  | optionUR (A : Cmra)
  | gmapUR (K : Ty) (V : Cmra)
end

end Syntax

namespace Syntax.Ty
def El : Ty → Type
  | .unit => Unit | .bool => Bool | .nat => Nat | .int => Int | .pos => Pos
  | .prod a b => a.El × b.El | .sum a b => a.El ⊕ b.El
  | .option a => Option a.El | .list a => List a.El

instance decEq : (t : Ty) → DecidableEq t.El
  | .unit => inferInstanceAs (DecidableEq Unit)
  | .bool => inferInstanceAs (DecidableEq Bool)
  | .nat => inferInstanceAs (DecidableEq Nat)
  | .int => inferInstanceAs (DecidableEq Int)
  | .pos => inferInstanceAs (DecidableEq Pos)
  | .prod a b => letI := decEq a; letI := decEq b; inferInstanceAs (DecidableEq (a.El × b.El))
  | .sum a b => letI := decEq a; letI := decEq b; inferInstanceAs (DecidableEq (a.El ⊕ b.El))
  | .option a => letI := decEq a; inferInstanceAs (DecidableEq (Option a.El))
  | .list a => letI := decEq a; inferInstanceAs (DecidableEq (List a.El))
end Syntax.Ty

universe w

/-- An OFE functor at universe `w`, with its contractivity. -/
abbrev OFunctorB := Σ F : OFunctorPre.{w, w, w}, OFunctorContractive F
/-- A CMRA functor at universe `w`. -/
abbrev RFunctorB := Σ F : OFunctorPre.{w, w, w}, RFunctorContractive F
/-- A unital CMRA functor at universe `w`. -/
abbrev URFunctorB := Σ F : OFunctorPre.{w, w, w}, URFunctorContractive F

/-! ## Positive naturals under addition -/

/-- Positive naturals as a CMRA: `⟨k⟩` stands for `k + 1`, the operation is addition, and there
is no core. (Iris' `Pos` is binary and lacks the arithmetic lemmas needed here.) -/
@[ext] structure positive where
  ofPred ::
  pred : Nat
  deriving DecidableEq

namespace positive
instance : Add positive := ⟨fun x y => ⟨x.pred + y.pred + 1⟩⟩
@[simp] theorem add_pred (x y : positive) : (x + y).pred = x.pred + y.pred + 1 := rfl
/-- Conversion from `Nat`, with `ofNat 0 = 1`. -/
def ofNat (n : Nat) : positive := ⟨n - 1⟩
/-- `1%positive`. -/
def one : positive := ⟨0⟩
instance : Std.Associative (α := positive) (· + ·) := ⟨fun _ _ _ => by ext; simp; omega⟩
instance : Std.Commutative (α := positive) (· + ·) := ⟨fun _ _ => by ext; simp; omega⟩
instance : COFE positive := COFE.ofDiscrete positive
instance : OFE.Discrete positive := ⟨id⟩
instance : CMRA positive := PosCommMonoidLike.instCMRA
instance : CMRA.Discrete positive := PosCommMonoidLike.instDiscrete
end positive

/-! ## Interpretation of the codes

The codes are interpreted as functors at any universe `w` (the universe of
`IProp GF`, which is above the step-index type): the data of the codes is in
`Type`, and is lifted with `ULift` (`constOFU`) where the functor is
constant. -/

def intO : Syntax.Ofe → OFunctorB.{w}
  | .unitO => ⟨constOFU.{w} Unit, inferInstance⟩
  | .leibnizO t => ⟨constOFU.{w} (DiscreteO t.El), inferInstance⟩
  | .laterO => ⟨LaterOF IdOF, inferInstance⟩
  | .discreteFunO t o =>
    letI := (intO o).2
    ⟨DiscreteFunOF (fun _ : t.El => (intO o).1), inferInstance⟩
  | .prodO a b =>
    letI := (intO a).2; letI := (intO b).2
    ⟨ProdOF (intO a).1 (intO b).1, inferInstance⟩

instance (o : Syntax.Ofe) : OFunctorContractive (intO.{w} o).1 := (intO o).2

mutual
def intF : Syntax.Cmra → RFunctorB.{w}
  | .authR A => letI := (intUF A).2; ⟨Auth.AuthRF (intUF A).1, inferInstance⟩
  | .gmapViewR K V =>
    letI := (intF V).2; letI := K.decEq
    ⟨HeapView.HeapViewURF (K := K.El) (H := GMap K.El) (intF V).1, inferInstance⟩
  | .agreeR A => ⟨AgreeRF (intO A).1, inferInstance⟩
  | .exclR A => ⟨Excl.ExclOF (intO A).1, inferInstance⟩
  | .monoListR A => ⟨MonoListRF (intO A).1, inferInstance⟩
  | .prodR A B => letI := (intF A).2; letI := (intF B).2; ⟨ProdOF (intF A).1 (intF B).1, inferInstance⟩
  | .optionR A => letI := (intF A).2; ⟨OptionOF (intF A).1, inferInstance⟩
  | .csumR A B => letI := (intF A).2; letI := (intF B).2; ⟨Csum.OF (intF A).1 (intF B).1, inferInstance⟩
  | .natR => ⟨constOFU.{w} Nat, inferInstance⟩
  | .maxNatR => ⟨constOFU.{w} MaxNat, inferInstance⟩
  | .fracR => ⟨constOFU.{w} Qp, inferInstance⟩
  | .dfracR => ⟨constOFU.{w} DFrac, inferInstance⟩
  | .positiveR => ⟨constOFU.{w} positive, inferInstance⟩
def intUF : Syntax.Ucmra → URFunctorB.{w}
  | .unitUR => ⟨constOFU.{w} Unit, inferInstance⟩
  | .natUR => ⟨constOFU.{w} Nat, inferInstance⟩
  | .maxNatUR => ⟨constOFU.{w} MaxNat, inferInstance⟩
  | .prodUR A B => letI := (intUF A).2; letI := (intUF B).2; ⟨ProdOF (intUF A).1 (intUF B).1, inferInstance⟩
  | .optionUR A => letI := (intF A).2; ⟨OptionOF (intF A).1, inferInstance⟩
  | .gmapUR K V =>
    letI := (intF V).2; letI := K.decEq
    ⟨PartialMap.PartialMapOF (GMap K.El) (intF V).1, inferInstance⟩
end

/-! ## The universal functor and `allG` -/

instance : DecidableEq Syntax.Cmra := fun _ _ => Classical.propDecidable _

instance (e : Syntax.Cmra) : RFunctorContractive (intF.{w} e).1 := (intF e).2
instance (e : Syntax.Ucmra) : URFunctorContractive (intUF.{w} e).1 := (intUF e).2

/-- The universal functor: `∏ e, option (intF e)`. -/
abbrev AllURF : OFunctorPre.{w, w, w} := DiscreteFunOF (fun e : Syntax.Cmra => OptionOF (intF.{w} e).1)

/-- One `ElemG` for the universal functor gives ghost state of every algebra
with a code. -/
class AllG (GF : outParam BundledGFunctors) where
  any_inG : ElemG GF AllURF

attribute [reducible, instance] AllG.any_inG

/-- A `BundledGFunctors` with the universal functor at slot 0. -/
def «allΣ» : BundledGFunctors := BundledGFunctors.default.set 0 ⟨AllURF, inferInstance⟩

/-- `AllG GF` for any `GF` that contains `AllURF` at some slot. -/
@[instance_reducible] def allGOfSlot {GF : BundledGFunctors} (τ : GType)
    (h : GF τ = ⟨AllURF, inferInstance⟩) : AllG GF := ⟨ElemG.ofEq τ h⟩

theorem «allΣ_slot» : «allΣ» 0 = ⟨AllURF, inferInstance⟩ :=
  (by simp [«allΣ», BundledGFunctors.set])

@[instance_reducible] def «allG_allΣ» : AllG «allΣ» := allGOfSlot 0 «allΣ_slot»

/-! ## Isomorphisms -/

/-- An isomorphism of OFEs. -/
structure OfeIso (A : Type _) (B : Type _) [OFE A] [OFE B] where
  to : A -n> B
  of : B -n> A
  of_to : ∀ a, of (to a) = a
  to_of : ∀ b, to (of b) = b

/-- An isomorphism of CMRAs. -/
structure CmraIso (A : Type _) (B : Type _) [CMRA A] [CMRA B] where
  to : A -C> B
  of : B -C> A
  of_to : ∀ a, of (to a) = a
  to_of : ∀ b, to (of b) = b

/-! ## Evidence that a CMRA has a code -/

/-- `IsTy A t`: the type `A` is denoted by the code `t`. -/
class IsTy (A : Type) (t : outParam Syntax.Ty) : Prop where
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
variable (PROP : Type w) [COFE PROP]

/-- `A` (with its OFE structure) is isomorphic to the denotation of `e` at `PROP`. -/
class IsOfe (A : Type _) [OFE A] (e : outParam Syntax.Ofe) where
  iso : OfeIso A ((intO.{w} e).1 PROP PROP)

/-- `A` (with its CMRA structure) is isomorphic to the denotation of `e` at `PROP`. -/
class IsCmra (A : Type _) [CMRA A] (e : outParam Syntax.Cmra) where
  iso : CmraIso A ((intF.{w} e).1 PROP PROP)

/-- `A` (with its unital CMRA structure) is isomorphic to the denotation of `e`
at `PROP`, preserving the unit. -/
class IsUcmra (A : Type _) [UCMRA A] (e : outParam Syntax.Ucmra) where
  iso : CmraIso A ((intUF.{w} e).1 PROP PROP)
  iso_unit : iso.to UCMRA.unit = UCMRA.unit

end denote

/-! ## Isomorphism toolkit -/

section iso_toolkit
open OFE CMRA

namespace OfeIso
variable {A B : Type _} [OFE A] [OFE B]

/-- The identity isomorphism. -/
def refl : OfeIso A A := ⟨OFE.Hom.id, OFE.Hom.id, fun _ => rfl, fun _ => rfl⟩

/-- `A` is isomorphic to `ULift A`. -/
def ulift : OfeIso A (ULift.{w} A) := ⟨uliftUpHom, uliftDownHom, fun _ => rfl, fun _ => rfl⟩

/-- Isomorphisms lift to products. -/
def prod {A' B' : Type _} [OFE A'] [OFE B'] (I : OfeIso A A') (J : OfeIso B B') :
    OfeIso (A × B) (A' × B') where
  to := ⟨Prod.map I.to J.to, ⟨fun _ _ _ h => ⟨I.to.ne.ne h.1, J.to.ne.ne h.2⟩⟩⟩
  of := ⟨Prod.map I.of J.of, ⟨fun _ _ _ h => ⟨I.of.ne.ne h.1, J.of.ne.ne h.2⟩⟩⟩
  of_to x := Prod.ext (I.of_to x.1) (J.of_to x.2)
  to_of x := Prod.ext (I.to_of x.1) (J.to_of x.2)

/-- Isomorphisms lift pointwise to (non-dependent) functions. -/
def pi {X : Type _} (I : OfeIso A B) : OfeIso (X → A) (X → B) where
  to := ⟨fun f x => I.to (f x), ⟨fun _ _ _ h x => I.to.ne.ne (h x)⟩⟩
  of := ⟨fun f x => I.of (f x), ⟨fun _ _ _ h x => I.of.ne.ne (h x)⟩⟩
  of_to f := funext fun x => I.of_to (f x)
  to_of f := funext fun x => I.to_of (f x)

/-- Isomorphisms lift to `Agree`. -/
def agree (I : OfeIso A B) : CmraIso (Agree A) (Agree B) where
  to := Agree.map I.to
  of := Agree.map I.of
  of_to x := (Agree.map_compose I.to I.of x).symm.trans
    ((Agree.agree_map_ext (f := I.of.comp I.to) (g := id) I.of_to).trans (Agree.map_id x))
  to_of x := (Agree.map_compose I.of I.to x).symm.trans
    ((Agree.agree_map_ext (f := I.to.comp I.of) (g := id) I.to_of).trans (Agree.map_id x))

/-- Isomorphisms lift to `Excl`. -/
def excl (I : OfeIso A B) : CmraIso (Excl A) (Excl B) where
  to := Excl.hom I.to
  of := Excl.hom I.of
  of_to x := by cases x <;> first | rfl | exact congrArg _ (I.of_to _)
  to_of x := by cases x <;> first | rfl | exact congrArg _ (I.to_of _)

end OfeIso

/-- The camera morphism `A -C> ULift A`. -/
def CMRA.Hom.uliftUp {A : Type _} [CMRA A] : A -C> ULift.{w} A where
  f := ULift.up
  ne := ⟨fun _ _ _ h => h⟩
  validN h := h
  pcore _ := rfl
  op _ _ := rfl

/-- The camera morphism `ULift A -C> A`. -/
def CMRA.Hom.uliftDown {A : Type _} [CMRA A] : ULift.{w} A -C> A where
  f := ULift.down
  ne := ⟨fun _ _ _ h => h⟩
  validN h := h
  pcore x := by
    change Option.map ULift.down (Option.map ULift.up (pcore x.down)) = pcore x.down
    cases pcore x.down <;> rfl
  op _ _ := rfl

theorem view_map_inv {A B A' B' : Type _} {R : ViewRel A B} {R' : ViewRel A' B'}
    (f : A → A') (f' : A' → A) (g : B → B') (g' : B' → B)
    (hf : ∀ a, f' (f a) = a) (hg : ∀ b, g' (g b) = b) (v : View R) :
    View.map R f' g' (View.map R' f g v) = v := by
  rw [← View.map_compose]
  have e1 : f' ∘ f = id := funext hf
  have e2 : g' ∘ g = id := funext hg
  rw [e1, e2, View.map_id]

namespace CmraIso
variable {A B : Type _} [CMRA A] [CMRA B]

/-- `A` is isomorphic to `ULift A`. -/
def ulift : CmraIso A (ULift.{w} A) :=
  ⟨CMRA.Hom.uliftUp, CMRA.Hom.uliftDown, fun _ => rfl, fun _ => rfl⟩

/-- Isomorphisms lift to `Option`. -/
def option (I : CmraIso A B) : CmraIso (Option A) (Option B) where
  to := Option.mapC I.to
  of := Option.mapC I.of
  of_to x := by cases x with | none => rfl | some a => exact congrArg some (I.of_to a)
  to_of x := by cases x with | none => rfl | some a => exact congrArg some (I.to_of a)

/-- Isomorphisms lift to products. -/
def prod {A' B' : Type _} [CMRA A'] [CMRA B'] (I : CmraIso A A') (J : CmraIso B B') :
    CmraIso (A × B) (A' × B') where
  to := Prod.mapC I.to J.to
  of := Prod.mapC I.of J.of
  of_to x := Prod.ext (I.of_to x.1) (J.of_to x.2)
  to_of x := Prod.ext (I.to_of x.1) (J.to_of x.2)

/-- Isomorphisms lift to `Csum`. -/
def csum {A' B' : Type _} [CMRA A'] [CMRA B'] (I : CmraIso A A') (J : CmraIso B B') :
    CmraIso (Csum A B) (Csum A' B') where
  to := Csum.cMap I.to J.to
  of := Csum.cMap I.of J.of
  of_to x := by
    cases x <;> first | rfl | exact congrArg _ (I.of_to _) | exact congrArg _ (J.of_to _)
  to_of x := by
    cases x <;> first | rfl | exact congrArg _ (I.to_of _) | exact congrArg _ (J.to_of _)

/-- Isomorphisms of unital cameras lift to `Auth`. -/
def auth {A B : Type _} [UCMRA A] [UCMRA B] (I : CmraIso A B) : CmraIso (Auth A) (Auth B) where
  to := View.mapC I.to.toHom I.to (Auth.authViewRel_map I.to)
  of := View.mapC I.of.toHom I.of (Auth.authViewRel_map I.of)
  of_to := view_map_inv _ _ _ _ I.of_to I.of_to
  to_of := view_map_inv _ _ _ _ I.to_of I.to_of

end CmraIso

section partialMaps
open Std

/-! Partial-map cameras whose value types live in different universes (e.g. `GMap K V` with
`V : Type` and `GMap K V'` with `V'` in the universe of `IProp`). iris-lean's
`PartialMap.mapC` stays inside a single map family `M : Type u → Type v`, so these maps are
described by their action on `get?` instead. -/

variable {K : Type _} {M : Type _ → Type _} {M' : Type _ → Type _}
  [LawfulPartialMap M K] [LawfulPartialMap M' K]

/-- A map between partial-map cameras that acts as the camera morphism `f` pointwise is a
camera morphism. -/
def pmapHom {A B : Type _} [CMRA A] [CMRA B] (f : A -C> B) (φ : M A → M' B)
    (hφ : ∀ m k, get? (φ m) k = (get? m k).map f) : M A -C> M' B where
  f := φ
  ne := ⟨fun _ m1 m2 h k => by rw [hφ, hφ]; exact (optionMap f.toHom).ne.ne (h k)⟩
  validN {_ m} h k := by rw [hφ]; exact (Option.mapC f).validN (h k)
  pcore m := by
    change some (φ _) = some _
    refine congrArg some (equiv_iff_eq.mp fun k => ?_)
    rw [hφ, get?_bindAlter, get?_bindAlter, hφ]
    cases get? m k with
    | none => rfl
    | some a => exact f.pcore a
  op m1 m2 := by
    refine equiv_iff_eq.mp fun k => ?_
    change get? (φ (merge _ m1 m2)) k = get? (merge _ (φ m1) (φ m2)) k
    rw [hφ, get?_merge, get?_merge, hφ, hφ]
    cases get? m1 k <;> cases get? m2 k <;> simp [Option.merge, f.op]

theorem pmap_inv {A B : Type _} (φ : M A → M' B) (ψ : M' B → M A) (f : A → B) (g : B → A)
    (hφ : ∀ m k, get? (φ m) k = (get? m k).map f) (hψ : ∀ m k, get? (ψ m) k = (get? m k).map g)
    (hgf : ∀ a, g (f a) = a) (m : M A) : ψ (φ m) = m :=
  equiv_iff_eq.mp fun k => by
    rw [hψ, hφ, Option.map_map]
    cases get? m k with
    | none => rfl
    | some a => exact congrArg some (hgf a)

/-- Isomorphisms lift to partial maps, given maps acting pointwise on `get?`. -/
def CmraIso.pmap {A B : Type _} [CMRA A] [CMRA B] (I : CmraIso A B) (φ : M A → M' B)
    (ψ : M' B → M A) (hφ : ∀ m k, get? (φ m) k = (get? m k).map I.to)
    (hψ : ∀ m k, get? (ψ m) k = (get? m k).map I.of) : CmraIso (M A) (M' B) where
  to := pmapHom I.to φ hφ
  of := pmapHom I.of ψ hψ
  of_to := pmap_inv φ ψ _ _ hφ hψ I.of_to
  to_of := pmap_inv ψ φ _ _ hψ hφ I.to_of

theorem pmap_empty {A B : Type _} (φ : M A → M' B) (f : A → B)
    (hφ : ∀ m k, get? (φ m) k = (get? m k).map f) : φ ∅ = ∅ :=
  equiv_iff_eq.mp fun k => by rw [hφ, get?_empty, get?_empty]; rfl

theorem heapR_pmap {V V' : Type _} [CMRA V] [CMRA V'] (g : V -C> V')
    (φ : M V → M' V') (φ₂ : M (DFrac × V) → M' (DFrac × V'))
    (hφ : ∀ m k, get? (φ m) k = (get? m k).map g)
    (hφ₂ : ∀ m k, get? (φ₂ m) k = (get? m k).map (Prod.mapC CMRA.Hom.id g))
    (n : SI) (m : M V) (mv : M (DFrac × V)) :
    HeapR K V M n m mv → HeapR K V' M' n (φ m) (φ₂ mv) := by
  intro hr k fv hk
  rw [hφ₂] at hk
  rcases hmv : get? mv k with _ | ⟨q, b⟩ <;> rw [hmv] at hk
  · cases hk
  · cases hk
    obtain ⟨v, dq, hv, hvalid, hinc⟩ := hr k (q, b) hmv
    refine ⟨g v, dq, by rw [hφ, hv]; rfl, ⟨hvalid.1, g.validN hvalid.2⟩, ?_⟩
    exact (Option.mapC (Prod.mapC CMRA.Hom.id g)).monoN n hinc

/-- Isomorphisms lift to heap views, given maps acting pointwise on `get?`. -/
def CmraIso.heapView {V V' : Type _} [CMRA V] [CMRA V'] (I : CmraIso V V')
    (φ : M V → M' V') (ψ : M' V' → M V)
    (φ₂ : M (DFrac × V) → M' (DFrac × V')) (ψ₂ : M' (DFrac × V') → M (DFrac × V))
    (hφ : ∀ m k, get? (φ m) k = (get? m k).map I.to)
    (hψ : ∀ m k, get? (ψ m) k = (get? m k).map I.of)
    (hφ₂ : ∀ m k, get? (φ₂ m) k = (get? m k).map (Prod.mapC CMRA.Hom.id I.to))
    (hψ₂ : ∀ m k, get? (ψ₂ m) k = (get? m k).map (Prod.mapC CMRA.Hom.id I.of)) :
    CmraIso (HeapView K V M) (HeapView K V' M') where
  to := View.mapC (pmapHom I.to φ hφ).toHom (pmapHom (Prod.mapC CMRA.Hom.id I.to) φ₂ hφ₂)
    (heapR_pmap I.to φ φ₂ hφ hφ₂)
  of := View.mapC (pmapHom I.of ψ hψ).toHom (pmapHom (Prod.mapC CMRA.Hom.id I.of) ψ₂ hψ₂)
    (heapR_pmap I.of ψ ψ₂ hψ hψ₂)
  of_to := view_map_inv _ _ _ _ (pmap_inv φ ψ _ _ hφ hψ I.of_to)
    (pmap_inv φ₂ ψ₂ _ _ hφ₂ hψ₂ fun x => Prod.ext rfl (I.of_to x.2))
  to_of := view_map_inv _ _ _ _ (pmap_inv ψ φ _ _ hψ hφ I.to_of)
    (pmap_inv ψ₂ φ₂ _ _ hψ₂ hφ₂ fun x => Prod.ext rfl (I.to_of x.2))

end partialMaps

/-- `GMap.map`, across universes. -/
def gmapMap {K : Type _} {V V' : Type _} (f : V → V') (m : GMap K V) : GMap K V' :=
  ⟨fun k => (m.lookup k).map f, by
    obtain ⟨l, hl⟩ := m.finite
    exact ⟨l, fun k h => hl k (by cases e : m.lookup k <;> simp_all)⟩⟩

theorem gmapMap_get? {K : Type _} [DecidableEq K] {V V' : Type _} (f : V → V') (m : GMap K V)
    (k : K) : Std.get? (gmapMap f m) k = (Std.get? m k).map f := rfl

theorem extTreeMap_map_get? {V V' : Type _} (f : V → V') (m : MaxPrefixListMap V) (k : Nat) :
    Std.get? (M := MaxPrefixListMap) (m.map fun _ => f) k = (Std.get? m k).map f :=
  Std.ExtTreeMap.getElem?_map

end iso_toolkit

section instances
variable {PROP : Type w} [COFE PROP]

instance is_unitO : IsOfe PROP Unit .unitO := ⟨OfeIso.ulift⟩
instance is_leibnizO [h : IsTy A t] : IsOfe PROP (DiscreteO A) (.leibnizO t) := by
  obtain ⟨rfl⟩ := h; exact ⟨OfeIso.ulift⟩
instance is_laterO : IsOfe PROP (Later PROP) .laterO := ⟨OfeIso.refl⟩
instance is_discrete_funO [ht : IsTy A t] [OFE B] [hB : IsOfe PROP B o] :
    IsOfe PROP (A → B) (.discreteFunO t o) := by
  obtain ⟨rfl⟩ := ht; exact ⟨hB.iso.pi⟩
instance is_prodO [OFE A] [OFE B] [hA : IsOfe PROP A a] [hB : IsOfe PROP B b] :
    IsOfe PROP (A × B) (.prodO a b) := ⟨hA.iso.prod hB.iso⟩

instance is_authR [UCMRA A] [hA : IsUcmra PROP A a] : IsCmra PROP (Auth A) (.authR a) :=
  ⟨hA.iso.auth⟩
instance is_gmap_viewR [hK : IsTy K k] [dK : DecidableEq K] [CMRA V] [hV : IsCmra PROP V v] :
    IsCmra PROP (HeapView K V (GMap K)) (.gmapViewR k v) := by
  obtain ⟨rfl⟩ := hK
  obtain rfl : dK = k.decEq := Subsingleton.elim _ _
  exact ⟨hV.iso.heapView (gmapMap hV.iso.to) (gmapMap hV.iso.of)
    (gmapMap (Prod.mapC CMRA.Hom.id hV.iso.to)) (gmapMap (Prod.mapC CMRA.Hom.id hV.iso.of))
    (gmapMap_get? _) (gmapMap_get? _) (gmapMap_get? _) (gmapMap_get? _)⟩
instance is_agreeR [OFE A] [hA : IsOfe PROP A a] : IsCmra PROP (Agree A) (.agreeR a) :=
  ⟨hA.iso.agree⟩
instance is_exclR [OFE A] [hA : IsOfe PROP A a] : IsCmra PROP (Excl A) (.exclR a) :=
  ⟨hA.iso.excl⟩
instance is_mono_listR [OFE A] [hA : IsOfe PROP A a] : IsCmra PROP (MonoList A) (.monoListR a) :=
  ⟨CmraIso.auth (hA.iso.agree.pmap (Std.ExtTreeMap.map fun _ => hA.iso.agree.to)
    (Std.ExtTreeMap.map fun _ => hA.iso.agree.of) (extTreeMap_map_get? _) (extTreeMap_map_get? _))⟩
instance is_prodR [CMRA A] [CMRA B] [hA : IsCmra PROP A a] [hB : IsCmra PROP B b] :
    IsCmra PROP (A × B) (.prodR a b) := ⟨hA.iso.prod hB.iso⟩
instance is_optionR [CMRA A] [hA : IsCmra PROP A a] : IsCmra PROP (Option A) (.optionR a) :=
  ⟨hA.iso.option⟩
instance is_csumR [CMRA A] [CMRA B] [hA : IsCmra PROP A a] [hB : IsCmra PROP B b] :
    IsCmra PROP (Csum A B) (.csumR a b) := ⟨hA.iso.csum hB.iso⟩
instance is_natR : IsCmra PROP Nat .natR := ⟨CmraIso.ulift⟩
instance is_max_natR : IsCmra PROP MaxNat .maxNatR := ⟨CmraIso.ulift⟩
instance is_fracR : IsCmra PROP Qp .fracR := ⟨CmraIso.ulift⟩
instance is_dfracR : IsCmra PROP DFrac .dfracR := ⟨CmraIso.ulift⟩
instance is_positiveR : IsCmra PROP positive .positiveR := ⟨CmraIso.ulift⟩

instance is_unitUR : IsUcmra PROP Unit .unitUR := ⟨CmraIso.ulift, rfl⟩
instance is_natUR : IsUcmra PROP Nat .natUR := ⟨CmraIso.ulift, rfl⟩
instance is_max_natUR : IsUcmra PROP MaxNat .maxNatUR := ⟨CmraIso.ulift, rfl⟩
instance is_prodUR [UCMRA A] [UCMRA B] [hA : IsUcmra PROP A a] [hB : IsUcmra PROP B b] :
    IsUcmra PROP (A × B) (.prodUR a b) :=
  ⟨hA.iso.prod hB.iso, Prod.ext hA.iso_unit hB.iso_unit⟩
instance is_optionUR [CMRA A] [hA : IsCmra PROP A a] : IsUcmra PROP (Option A) (.optionUR a) :=
  ⟨hA.iso.option, rfl⟩
instance is_gmapUR [hK : IsTy K k] [dK : DecidableEq K] [CMRA V] [hV : IsCmra PROP V v] :
    IsUcmra PROP (GMap K V) (.gmapUR k v) := by
  obtain ⟨rfl⟩ := hK
  obtain rfl : dK = k.decEq := Subsingleton.elim _ _
  exact ⟨hV.iso.pmap (gmapMap hV.iso.to) (gmapMap hV.iso.of) (gmapMap_get? _) (gmapMap_get? _),
    pmap_empty _ _ (gmapMap_get? _)⟩

end instances


/-! ## Ownership -/

section own
open BI OFE CMRA ProofMode

variable {GF : BundledGFunctors} [AllG GF]

/-- Ownership of `a : A` at ghost name `γ`, for any `A` with a code. -/
def own {A : Type _} [CMRA A] {e : outParam Syntax.Cmra} [H : IsCmra (IProp GF) A e]
    (γ : GName) (a : A) : IProp GF :=
  iOwn (F := AllURF) γ (discreteFunSingleton e (some (H.iso.to a)))

variable {A : Type _} [CMRA A] {e : Syntax.Cmra} [H : IsCmra (IProp GF) A e]

/-! Generic facts about camera isomorphisms. -/
namespace CmraIso
variable {A B : Type _} [CMRA A] [CMRA B] (I : CmraIso A B)

theorem of_dist {n : SI} {a : A} {b : B} (h : I.to a ≡{n}≡ b) : a ≡{n}≡ I.of b := by
  have := I.of.ne.ne h; rwa [I.of_to] at this

theorem validN_iff {n : SI} {a : A} : ✓{n} I.to a ↔ ✓{n} a :=
  ⟨fun h => I.of_to a ▸ I.of.validN h, I.to.validN⟩

theorem valid_iff {a : A} : ✓ I.to a ↔ ✓ a := by
  rw [valid_iff_validN, valid_iff_validN]; exact forall_congr' fun _ => I.validN_iff

theorem discreteE {a : A} [DiscreteE a] : DiscreteE (I.to a) :=
  ⟨fun {y} h => by rw [DiscreteE.discrete (I.of_dist h), I.to_of]⟩

theorem coreId {a : A} [CoreId a] : CoreId (I.to a) :=
  ⟨by rw [← I.to.pcore, CoreId.core_id]; rfl⟩

theorem updateP {a : A} {P : A → Prop} (h : a ~~>: P) :
    I.to a ~~>: fun y => ∃ a', y = I.to a' ∧ P a' := by
  intro n mz hv
  have hv' : ✓{n} (a •? mz.map I.of) := by
    have := I.of.validN hv
    cases mz with
    | none => change ✓{n} I.of (I.to a) at this; rwa [I.of_to] at this
    | some z => change ✓{n} I.of (I.to a • z) at this; rwa [I.of.op, I.of_to] at this
  obtain ⟨y, hy, hvy⟩ := h n _ hv'
  refine ⟨I.to y, ⟨y, rfl, hy⟩, ?_⟩
  have := I.to.validN hvy
  cases mz with
  | none => exact this
  | some z => change ✓{n} I.to (y • I.of z) at this; rwa [I.to.op, I.to_of] at this

end CmraIso

private theorem incN_mono {PROP : Type _} [Sbi PROP] {A B : Type _} [CMRA A] [CMRA B]
    {a b : A} {a' b' : B} (h : ∀ n, a ≼{n} b → a' ≼{n} b') : a ≼ b ⊢@{PROP} a' ≼ b' :=
  siPure_mono fun n hn => SiProp.exists_holds.mpr (h n (SiProp.exists_holds.mp hn))

instance own_ne (γ : GName) : NonExpansive (own (A := A) (GF := GF) γ) where
  ne {_ _ _} h := by
    unfold own
    exact iOwn_ne.ne ((instDiscreteFunSingletonNonExpansive e).ne
      (OFE.some_dist_some.mpr (H.iso.to.ne.ne h)))

theorem own_op (γ : GName) (a1 a2 : A) : own γ (a1 • a2) ⊣⊢ own γ a1 ∗ own γ a2 := by
  unfold own
  rw [H.iso.to.op, show (some (H.iso.to a1 • H.iso.to a2)) =
    (some (H.iso.to a1) • some (H.iso.to a2) : Option _) from rfl, ← discreteFunSingleton_op_eq]
  exact iOwn_op

theorem own_valid (γ : GName) (a : A) : own γ a ⊢ ✓ a := by
  unfold own
  refine iOwn_cmraValid.trans (internalCmraValid_entails.mpr fun n h => ?_)
  rw [discreteFunSingleton_validN_iff] at h
  exact H.iso.validN_iff.mp h

instance own_timeless (γ : GName) (a : A) [DiscreteE a] : Timeless (own γ a) := by
  unfold own
  haveI := H.iso.discreteE (a := a)
  haveI : ∀ i, DiscreteE (UCMRA.unit : Option ((intF i).1 (IProp GF) (IProp GF))) :=
    fun _ => Option.none_is_discrete
  exact iOwn_timeless

instance own_core_persistent (γ : GName) (a : A) [CoreId a] : Persistent (own γ a) := by
  unfold own
  haveI := H.iso.coreId (a := a)
  infer_instance

/-- Like iris-lean's `later_iOwn`, this needs finite step indices. -/
theorem later_own [SIdxFinite SI] (γ : GName) (a : A) :
    ▷ own γ a ⊢ ◇ ∃ b, own γ b ∧ ▷ (a ≡ b) := by
  unfold own
  have hev : NonExpansive (fun g : AllURF.ap (IProp GF) => g e) := ⟨fun _ _ _ h => h e⟩
  refine later_iOwn.trans ((except0_mono (exists_elim fun b' => ?_)).trans except0_idem.1)
  have hproj : ▷ (discreteFunSingleton e (some (H.iso.to a)) ≡ b') ⊢@{IProp GF}
      ▷ (some (H.iso.to a) ≡ b' e) := by
    refine later_mono ((internalEq.of_internalEquiv_ne (fun g : AllURF.ap (IProp GF) => g e)).trans ?_)
    simp only [discreteFunSingleton_self]
    exact .rfl
  rcases hb : b' e with _ | d
  · rw [hb] at hproj
    exact and_elim_r.trans (hproj.trans ((later_mono (option_some_none_equivI _).1).trans or_intro_l))
  · rw [hb] at hproj
    refine .trans ?_ except0_intro
    refine exists_intro_trans (H.iso.of d) (and_mono ?_ (hproj.trans (later_mono ?_)))
    · rw [H.iso.to_of]
      exact iOwn_mono ⟨discreteFunInsert e UCMRA.unit b',
        (discreteFunSingleton_op_insert (by rw [hb]; rfl)).symm⟩
    · refine (option_some_equivI _ _).1.trans ((internalEq.of_internalEquiv_ne H.iso.of.f).trans ?_)
      rw [H.iso.of_to]

theorem own_forall {B : Type _} [Inhabited B] (γ : GName) (f : B → A) :
    (∀ b, own γ (f b)) ⊢ ∃ c, own γ c ∗ ∀ b, some (f b) ≼ some c := by
  unfold own
  refine (iOwn_forall (F := AllURF) γ (fun b => discreteFunSingleton e (some (H.iso.to (f b))))).trans
    (exists_elim fun c => ?_)
  rcases hc : c e with _ | d
  · refine sep_elim_right.trans ((forall_elim default).trans ?_)
    refine (internalCmraIncluded_pure (φ := False) fun n => ⟨fun h => ?_, False.elim⟩).1.trans
      (pure_elim' False.elim)
    rcases Option.some_incN_some_iff.mp h with h | ⟨z, hz⟩
    · have h1 := h e; rw [hc, discreteFunSingleton_self] at h1; exact h1
    · have h1 : c e ≡{n}≡ _ • z e := hz e
      rw [hc, discreteFunSingleton_self] at h1
      rcases hz' : z e with _ | w <;> rw [hz'] at h1 <;> exact h1
  · refine exists_intro_trans (H.iso.of d) (sep_mono ?_ (forall_mono fun b => incN_mono ?_))
    · rw [H.iso.to_of]
      exact iOwn_mono ⟨discreteFunInsert e UCMRA.unit c,
        (discreteFunSingleton_op_insert (by rw [hc]; rfl)).symm⟩
    · intro n h
      refine Option.some_incN_some_iff.mpr ?_
      rcases Option.some_incN_some_iff.mp h with h | ⟨z, hz⟩
      · have h1 := h e; rw [hc, discreteFunSingleton_self] at h1
        exact .inl (H.iso.of_dist (OFE.some_dist_some.mp h1))
      · have h1 : c e ≡{n}≡ _ • z e := hz e
        rw [hc, discreteFunSingleton_self] at h1
        rcases hz' : z e with _ | w <;> rw [hz'] at h1
        · exact .inl (H.iso.of_dist (OFE.some_dist_some.mp h1).symm)
        · refine .inr ⟨H.iso.of w, ?_⟩
          have h2 := H.iso.of.ne.ne (OFE.some_dist_some.mp h1)
          rwa [H.iso.of.op, H.iso.of_to] at h2

theorem own_updateP (P : A → Prop) (γ : GName) (a : A) (Hupd : a ~~>: P) :
    own γ a ⊢ |==> ∃ a', ⌜P a'⌝ ∗ own γ a' := by
  unfold own
  have hupd : discreteFunSingleton (β := fun i => Option ((intF i).1 (IProp GF) (IProp GF))) e
      (some (H.iso.to a)) ~~>:
      fun g => ∃ a', g = discreteFunSingleton e (some (H.iso.to a')) ∧ P a' :=
    discreteFunSingleton_updateP _
      (UpdateP.option (Q := fun o => ∃ a', o = some (H.iso.to a') ∧ P a') (H.iso.updateP Hupd)
        fun _ ⟨a', hy, HP⟩ => ⟨a', hy ▸ rfl, HP⟩)
      fun _ ⟨a', hy, HP⟩ => ⟨a', hy ▸ rfl, HP⟩
  refine (iOwn_updateP hupd).trans (bupd_mono ?_)
  iintro ⟨%g, %hg, Hown⟩
  obtain ⟨a', rfl, HP⟩ := hg
  iexists a'
  isplitr
  · ipureintro; exact HP
  · iexact Hown

theorem own_alloc_strong_dep (f : GName → A) (P : GName → Prop) (HP : PredInfinite P)
    (Hf : ∀ γ, P γ → ✓ f γ) : ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ (f γ) := by
  unfold own
  exact iOwn_alloc_strong_dep _ P HP.exists_ge fun γ hγ =>
    (discreteFunSingleton_valid_iff _).mpr (H.iso.valid_iff.mpr (Hf γ hγ))

theorem own_unit {B : Type _} [UCMRA B] {e : Syntax.Cmra} [HB : IsCmra (IProp GF) B e]
    (γ : GName) : ⊢ |==> own γ (UCMRA.unit : B) := by
  unfold own
  have hup : (UCMRA.unit : Option ((intF e).1 (IProp GF) (IProp GF))) ~~>
      some (HB.iso.to UCMRA.unit) := by
    intro n mz hv
    rcases mz with _ | _ | z
    · exact HB.iso.validN_iff.mpr CMRA.unit_validN
    · exact HB.iso.validN_iff.mpr CMRA.unit_validN
    · show ✓{n} (HB.iso.to UCMRA.unit • z)
      rw [← HB.iso.to_of z, ← HB.iso.to.op, UCMRA.unit_left_id, HB.iso.to_of]
      exact hv
  exact iOwn_unit.trans (bupd_mono (iOwn_update (discreteFunSingleton_update_unit hup)) |>.trans
    bupd_trans)

end own
end Perennial
