/-
Port of `new/golang/theory/postlifting.v`: the typed points-to `l ↦{dq} v`,
the classes `TypedPointsto`, `IntoValTypedUnderlying` and `IntoValTyped`, WPs
for basic Go instructions, and the typed points-to instances for primitive
types.

Differences from Rocq:
* `countable_interface` (admitted in Rocq) is omitted: `gmap` only needs
  `DecidableEq`.
* The Rocq `Hint Extern`s proving `go.NotNamed t`/`go.NotInterface t` by
  computation are replaced by one instance per constructor of `go.GoType`. A type
  hidden behind a (non-reducible) definition is therefore not seen through; make
  such definitions `@[reducible]` (or state the instance).
* `IntoValTyped.wp_load` is not exported (it would clash with the untyped
  `Perennial.wp_load` of `GooseLang/Lifting.lean`, Rocq's `lifting.wp_load`);
  write `IntoValTyped.wp_load`. `wp_alloc` and `wp_store` are exported.
* The typed points-to notation is `l ↦{dq} v`, `l ↦ v` (full ownership) and
  `l ↦□ v` (discarded), scoped to `Perennial`.
-/
import Perennial.Golang.Theory.ProofMode
import Perennial.Golang.Theory.Display
import Perennial.Golang.Defn.Pre
import Perennial.Helpers.NamedProps
import Perennial.IrisLib.DFractional

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-! ## `PureWp` for calls of Go function values

(The last of the basic `PureWp` instances of `ProofMode.lean`, here because it needs
`go.PreSemantics`.) -/

section instances
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

instance wp_call_go_func (v2 : val) (f x : Binder) (e : Expr) :
    PureWp (G := G) (L := L) True (App (Val #(func.mk f x e)) (Val v2))
      (subst' x v2 (subst' f #(func.mk f x e) e)) := by
  have h : (#(func.mk f x e) : val) = RecV f x e := by
    rw [go.intoVal_unfold func.t]
  rw [h]
  exact pure_exec_pure_wp (pure_beta f x e v2)

end instances

/-! ## Underlying-type instances -/

section underlying_instances
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]

instance (priority := 100) underlying_eq (t : go.GoType) : t ≤u t := ⟨rfl⟩

instance unfold_to_underlying_eq {t t' : go.GoType} [h : t <u t'] : t ≤u t' :=
  ⟨h.underlying_unfold⟩

instance is_underlying_unfold {t t' tunder : go.GoType} [h : t <u t'] [h' : t' ↓u tunder] :
    t ↓u tunder :=
  ⟨h.underlying_unfold.trans h'.is_underlying⟩

theorem underlying_trivial (t : go.GoType) : t ↓u (underlying t) := ⟨rfl⟩

end underlying_instances

/-- `go.go_zero_val_step` with the `ZeroVal V` instance determined by the
`TypeRepr t V` instance (the Rocq-order binder `[ZeroVal V]` first makes Lean's
typeclass search get stuck on `ZeroVal ?V`). -/
instance (priority := high) go_zero_val_step' [FfiSyntax] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] [go.CoreSemantics] {V : Type} {zv : ZeroVal V} {t : go.GoType}
    [TypeRepr t V] : ⟦GoZeroVal t, #()⟧ ⤳ #(zero_val V) :=
  go.go_zero_val_step

/-- `go.structFieldRef_step` with the `ZeroVal V` instance determined by
`TypeRepr t V` (see `go_zero_val_step'`). -/
instance (priority := high) structFieldRef_step' [FfiSyntax] [GoLocalContext]
    [GoGlobalContext] [GoSemanticsFunctions] [go.CoreSemantics] (t : go.GoType) (f : GoString)
    (l : Loc) {V : Type} {zv : ZeroVal V} [TypeRepr t V] :
    ⟦StructFieldRef t f, #l⟧ ⤳[under] #(structFieldRef V f l) :=
  go.structFieldRef_step t f l

section not_named
instance notNamed_ArrayType (n : Int) (t : go.GoType) : go.NotNamed (go.ArrayType n t) := ⟨trivial⟩
instance notNamed_StructType (fds : List go.field_decl) : go.NotNamed (go.StructType fds) :=
  ⟨trivial⟩
instance notNamed_PointerType (t : go.GoType) : go.NotNamed (go.PointerType t) := ⟨trivial⟩
instance notNamed_FunctionType (sig : go.signature) : go.NotNamed (go.FunctionType sig) :=
  ⟨trivial⟩
instance notNamed_InterfaceType (elems : List go.InterfaceElem) :
    go.NotNamed (go.InterfaceType elems) := ⟨trivial⟩
instance notNamed_SliceType (t : go.GoType) : go.NotNamed (go.SliceType t) := ⟨trivial⟩
instance notNamed_MapType (k v : go.GoType) : go.NotNamed (go.MapType k v) := ⟨trivial⟩
instance notNamed_ChannelType (d : go.ChanDir) (t : go.GoType) :
    go.NotNamed (go.ChannelType d t) := ⟨trivial⟩
instance notNamed_UntypedType (n : go.TypeName) : go.NotNamed (go.UntypedType n) := ⟨trivial⟩

instance notInterface_Named (n : go.TypeName) (args : List go.GoType) :
    go.NotInterface (go.Named n args) := ⟨trivial⟩
instance notInterface_ArrayType (n : Int) (t : go.GoType) : go.NotInterface (go.ArrayType n t) :=
  ⟨trivial⟩
instance notInterface_StructType (fds : List go.field_decl) :
    go.NotInterface (go.StructType fds) := ⟨trivial⟩
instance notInterface_PointerType (t : go.GoType) : go.NotInterface (go.PointerType t) := ⟨trivial⟩
instance notInterface_FunctionType (sig : go.signature) :
    go.NotInterface (go.FunctionType sig) := ⟨trivial⟩
instance notInterface_SliceType (t : go.GoType) : go.NotInterface (go.SliceType t) := ⟨trivial⟩
instance notInterface_MapType (k v : go.GoType) : go.NotInterface (go.MapType k v) := ⟨trivial⟩
instance notInterface_ChannelType (d : go.ChanDir) (t : go.GoType) :
    go.NotInterface (go.ChannelType d t) := ⟨trivial⟩
instance notInterface_UntypedType (n : go.TypeName) : go.NotInterface (go.UntypedType n) :=
  ⟨trivial⟩
end not_named

/-! ## Typed points-to -/

section typed_pointsto_defs
variable {GF : BundledGFunctors}

/-- `TypedPointsto V` gives the typed points-to `l ↦{dq} v` for values `v : V`
(it does not mention a Go type: several Go types can share a Lean
representation `V`). -/
class TypedPointsto (V : Type) where
  typedPointstoDef : Loc → V → DFrac → IProp GF
  typedPointstoDef_dfractional : ∀ l v, DFractional (typedPointstoDef l v)
  typedPointstoDef_timeless : ∀ l v dq, Timeless (typedPointstoDef l v dq)
  typedPointsto_agree : ∀ l dq1 dq2 (v1 v2 : V),
    typedPointstoDef l v1 dq1 ⊢ typedPointstoDef l v2 dq2 -∗ ⌜v1 = v2⌝

export TypedPointsto (typedPointstoDef typedPointstoDef_dfractional
  typedPointstoDef_timeless typedPointsto_agree)

def typedPointstoWrap {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (dq : DFrac) :
    IProp GF :=
  iprop(typedPointstoDef (GF := GF) l v dq ∗ ⌜l ≠ null⌝)

/-- The typed points-to `l ↦{dq} v` (sealed). -/
@[irreducible] def typedPointsto {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V)
    (dq : DFrac) : IProp GF :=
  typedPointstoWrap l v dq

theorem typedPointsto_unseal :
    @typedPointsto GF = @typedPointstoWrap GF := by
  funext V _ l v dq; with_unfolding_all rfl

theorem typedPointsto_unseal_eq {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V)
    (dq : DFrac) :
    typedPointsto l v dq = iprop(typedPointstoDef (GF := GF) l v dq ∗ ⌜l ≠ null⌝) := by
  rw [typedPointsto_unseal]; rfl

end typed_pointsto_defs

/-- `l ↦{dq} v`: typed points-to. -/
scoped notation:50 l:50 " ↦{" dq "} " v:50 => typedPointsto l v dq
/-- `l ↦ v`: typed points-to with full ownership. -/
scoped notation:50 l:50 " ↦ " v:50 => typedPointsto l v (DFrac.own 1)
/-- `l ↦□ v`: persistent typed points-to. -/
scoped notation:50 l:50 " ↦□ " v:50 => typedPointsto l v DFrac.discard

section typed_pointsto_props
variable {GF : BundledGFunctors}
open ProofMode

/-- For empty struct types. -/
instance true_dfractional : DFractional (fun (_ : DFrac) => (iprop(True) : IProp GF)) where
  dfractional _ _ := ⟨by iintro _; isplit <;> itrivial, by iintro _; itrivial⟩
  dfractional_persistent := inferInstance
  dfractional_persist _ := by iintro _; imodintro; itrivial

variable {V : Type} [TypedPointsto (GF := GF) V]

instance typedPointsto_dfractional (l : Loc) (v : V) :
    DFractional (fun dq => typedPointsto (GF := GF) l v dq) := by
  rw [typedPointsto_unseal]
  have := typedPointstoDef_dfractional (GF := GF) l v
  unfold typedPointstoWrap
  infer_instance

instance typedPointsto_timeless (l : Loc) (dq : DFrac) (v : V) :
    Timeless (typedPointsto (GF := GF) l v dq) := by
  rw [typedPointsto_unseal]
  have := typedPointstoDef_timeless (GF := GF) l v dq
  unfold typedPointstoWrap
  infer_instance

instance typedPointsto_as_dfractional (l : Loc) (dq : DFrac) (v : V) :
    AsDFractional (typedPointsto (GF := GF) l v dq) (fun dq => typedPointsto l v dq) dq :=
  ⟨.rfl, typedPointsto_dfractional l v⟩

instance typedPointsto_persistent (l : Loc) (v : V) :
    Persistent (typedPointsto (GF := GF) l v .discard) :=
  (typedPointsto_dfractional (GF := GF) l v).dfractional_persistent

instance typedPointsto_combine_sep_gives (l : Loc) (dq1 dq2 : DFrac) (v1 v2 : V) :
    CombineSepGives (typedPointsto (GF := GF) l v1 dq1) (typedPointsto l v2 dq2)
      iprop(⌜v1 = v2⌝) where
  combine_sep_gives := by
    rw [typedPointsto_unseal]; unfold typedPointstoWrap
    iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
    icases typedPointsto_agree l dq1 dq2 v1 v2 $$ H1 H2 with %Heq
    imodintro; ipureintro; exact Heq

theorem typedPointsto_split (l : Loc) (v : V) (dq : DFrac) :
    typedPointsto (GF := GF) l v dq ⊢ typedPointstoDef l v dq := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  iintro ⟨H, _⟩; iexact H

theorem typedPointsto_combine (l : Loc) (v : V) (dq : DFrac) (h : l ≠ null) :
    typedPointstoDef (GF := GF) l v dq ⊢ typedPointsto l v dq := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  iintro H; iframe H; ipureintro; exact h

theorem typedPointsto_not_null (l : Loc) (v : V) (dq : DFrac) :
    typedPointsto (GF := GF) l v dq ⊢ ⌜l ≠ null⌝ := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  iintro ⟨_, %h⟩; ipureintro; exact h

end typed_pointsto_props

/-! ## `IntoValTyped` -/

section into_val_defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- `IntoValTypedUnderlying V t_under` provides proofs that allocating, loading
and storing at any type `t` with underlying type `t_under` respects the typed
points-to for `V`. -/
class IntoValTypedUnderlying (V : outParam Type) (t_under : go.GoType) [ZeroVal V]
    [TypedPointsto (GF := GF) V] [GoSemanticsFunctions] : Prop where
  wp_alloc_def : ∀ {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u t_under] (v : V),
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoAlloc t))) (Val #v)) @ s; E
    {{ (l : Loc), RET #l; l ↦ v }}
  wp_load_def : ∀ {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u t_under] (l : Loc)
      (dq : DFrac) (v : V),
    {{ (l ↦{dq} v : IProp GF) }} (App (Val (GoInstruction (GoLoad t))) (Val #l)) @ s; E
    {{ RET #v; l ↦{dq} v }}
  wp_store_def : ∀ {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u t_under] (l : Loc)
      (v w : V),
    {{ (l ↦ v : IProp GF) }} (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w))) @ s; E
    {{ RET #(); l ↦ w }}
  type_repr_def : go.TypeReprUnderlying t_under V

/-- `IntoValTyped V t`: allocating, loading and storing at Go type `t` respects
the typed points-to for `V`. -/
class IntoValTyped (V : outParam Type) (t : go.GoType) [ZeroVal V] [TypedPointsto (GF := GF) V]
    [GoSemanticsFunctions] : Prop where
  wp_alloc : ∀ {s : Stuckness} {E : CoPset} (v : V),
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoAlloc t))) (Val #v)) @ s; E
    {{ (l : Loc), RET #l; l ↦ v }}
  wp_load : ∀ {s : Stuckness} {E : CoPset} (l : Loc) (dq : DFrac) (v : V),
    {{ (l ↦{dq} v : IProp GF) }} (App (Val (GoInstruction (GoLoad t))) (Val #l)) @ s; E
    {{ RET #v; l ↦{dq} v }}
  wp_store : ∀ {s : Stuckness} {E : CoPset} (l : Loc) (v w : V),
    {{ (l ↦ v : IProp GF) }} (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w))) @ s; E
    {{ RET #(); l ↦ w }}
  [type_repr : TypeRepr t V]

attribute [instance] IntoValTyped.type_repr
export IntoValTyped (wp_alloc wp_store)

instance underlying_to_into_val_typed {V : Type} {t_under : go.GoType} {zv : ZeroVal V}
    {tp : TypedPointsto (GF := GF) V} [GoSemanticsFunctions] [go.PreSemantics] {t : go.GoType}
    [t ↓u t_under] [h : IntoValTypedUnderlying (GF := GF) V t_under] :
    IntoValTyped (GF := GF) V t where
  wp_alloc v := h.wp_alloc_def v
  wp_load l dq v := h.wp_load_def l dq v
  wp_store l v w := h.wp_store_def l v w
  type_repr := by
    have := h.type_repr_def
    infer_instance

end into_val_defs

/-! ## WPs for basic Go instructions -/

section go_wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

instance pure_wp_go_step_det (i : GoInstruction) (v : val) (e : Expr)
    [h : go.IsGoStepPureDet i v e] :
    PureWp (G := G) (L := L) True (App (Val (GoInstruction i)) (Val v)) e where
  pure_wp_wp s E Φ K _ := by
    have hdet := h.isGoStep_det
    have hpure := h.isGoStep_pure_det
    iintro HΦ
    iapply wp_GoInstruction K i v Φ (fun gs => ⟨e, gs, (hdet gs gs e).2 ⟨by rw [hpure], rfl⟩⟩)
    inext
    iintro %e' %gs %gs' %Hstep Hlc Hctx
    obtain ⟨Hp, rfl⟩ := (hdet gs gs' e').1 Hstep
    rw [hpure] at Hp
    subst Hp
    imodintro
    iframe Hctx
    iapply HΦ $$ Hlc

/-- (Lean addition, time receipts) A deterministic pure Go instruction step
that also yields an exclusive time receipt `⧗ 1` (`wp_GoInstruction_receipt`).
Use it with `wp_bind` on the instruction, before `wp_auto` takes the step. -/
theorem wp_go_step_receipt (i : GoInstruction) (v : val) (e : Expr)
    [h : go.IsGoStepPureDet i v e] {s : Stuckness} {E : CoPset} (Φ : val → IProp GF)
    (K : List EctxItem) :
    ▷ (⧗ 1 -∗ £ 1 -∗ WP (fill K e) @ s; E {{ Φ }})
    ⊢ WP (fill K (App (Val (GoInstruction i)) (Val v))) @ s; E {{ Φ }} := by
  have hdet := h.isGoStep_det
  have hpure := h.isGoStep_pure_det
  iintro HΦ
  iapply wp_GoInstruction_receipt K i v Φ (fun gs => ⟨e, gs, (hdet gs gs e).2 ⟨by rw [hpure], rfl⟩⟩)
  inext
  iintro %e' %gs %gs' %Hstep Hlc Hr Hctx
  obtain ⟨Hp, rfl⟩ := (hdet gs gs' e').1 Hstep
  rw [hpure] at Hp
  subst Hp
  imodintro
  iframe Hctx
  iapply HΦ $$ Hr Hlc

/-- `wp_go_step_receipt` with an empty evaluation context (use after `wp_bind`). -/
theorem wp_go_step_receipt' (i : GoInstruction) (v : val) (e : Expr)
    [h : go.IsGoStepPureDet i v e] {s : Stuckness} {E : CoPset} (Φ : val → IProp GF) :
    ▷ (⧗ 1 -∗ £ 1 -∗ WP e @ s; E {{ Φ }})
    ⊢ WP (App (Val (GoInstruction i)) (Val v)) @ s; E {{ Φ }} :=
  wp_go_step_receipt i v e Φ []

/-- `wp_go_step_receipt` that also increments a persistent time receipt. -/
theorem wp_go_step_preceipt (i : GoInstruction) (v : val) (e : Expr)
    [h : go.IsGoStepPureDet i v e] {s : Stuckness} {E : CoPset} (Φ : val → IProp GF)
    (K : List EctxItem) (m : Nat) :
    ⧖ m ∗ ▷ (⧗ 1 -∗ ⧖ (m + 1) -∗ £ 1 -∗ WP (fill K e) @ s; E {{ Φ }})
    ⊢ WP (fill K (App (Val (GoInstruction i)) (Val v))) @ s; E {{ Φ }} := by
  have hdet := h.isGoStep_det
  have hpure := h.isGoStep_pure_det
  iintro ⟨Hm, HΦ⟩
  iapply wp_GoInstruction_preceipt K i v Φ m (fun gs => ⟨e, gs, (hdet gs gs e).2 ⟨by rw [hpure], rfl⟩⟩)
  iframe Hm
  inext
  iintro %e' %gs %gs' %Hstep Hlc Hr Hm' Hctx
  obtain ⟨Hp, rfl⟩ := (hdet gs gs' e').1 Hstep
  rw [hpure] at Hp
  subst Hp
  imodintro
  iframe Hctx
  iapply HΦ $$ Hr Hm' Hlc

variable {s : Stuckness} {E : CoPset}

theorem wp_GoPrealloc :
    {{ (True : IProp GF) }} (App (Val (GoInstruction GoPrealloc)) (Val #())) @ s; E
    {{ (l : Loc), RET #l; ⌜l ≠ null⌝ }} := by
  iintro %Φ _ HΦ
  have hstep : is_go_step_pure GoPrealloc #() = _ := go.go_prealloc_step
  iapply wp_GoInstruction' (s := s) (E := E) GoPrealloc #() Φ
    (fun gs => ⟨Val #(⟨1, 1⟩ : Loc), gs, by
      refine ⟨?_, rfl⟩
      show is_go_step_pure GoPrealloc #() _
      rw [hstep]; exact ⟨⟨1, 1⟩, by simp [null], rfl⟩⟩)
  inext
  iintro %e' %gs %gs' %Hstep _ Hctx
  obtain ⟨Hp, rfl⟩ := Hstep
  have Hp' : is_go_step_pure GoPrealloc #() e' := Hp
  rw [hstep] at Hp'
  obtain ⟨l, Hl, rfl⟩ := Hp'
  imodintro
  iframe Hctx
  iapply wp_value'
  iapply HΦ
  ipureintro; exact Hl

theorem wp_AngelicExit (Φ : val → IProp GF) :
    ⊢ WP (App (Val (GoInstruction AngelicExit)) (Val #())) @ s; E {{ Φ }} := by
  have hstep : is_go_step_pure AngelicExit #() = _ := go.angelic_exit_step
  iloeb as IH
  iapply wp_GoInstruction' (s := s) (E := E) AngelicExit #() Φ
    (fun gs => ⟨_, gs, by
      refine ⟨?_, rfl⟩
      show is_go_step_pure AngelicExit #() _
      rw [hstep]⟩)
  inext
  iintro %e' %gs %gs' %Hstep _ Hctx
  obtain ⟨Hp, rfl⟩ := Hstep
  have Hp' : is_go_step_pure AngelicExit #() e' := Hp
  rw [hstep] at Hp'
  subst Hp'
  imodintro
  iframe Hctx
  iexact IH

theorem wp_PackageInitCheck (pkg : GoString) (σ : GMap GoString Bool) :
    {{ ownGoState (GF := GF) σ }} (App (Val (GoInstruction (PackageInitCheck pkg))) (Val #())) @ s; E
    {{ RET #((σ !! pkg).getD false); ownGoState σ }} := by
  iintro %Φ Hown HΦ
  iapply wp_GoInstruction' (s := s) (E := E) (PackageInitCheck pkg) #() Φ
    (fun gs => ⟨_, gs, rfl, rfl, rfl⟩)
  inext
  iintro %e' %gs %gs' %Hstep _ Hauth
  obtain ⟨-, rfl, rfl⟩ := Hstep
  icombine Hauth Hown gives %Heq
  subst Heq
  imodintro
  iframe Hauth
  iapply wp_value'
  iapply HΦ $$ Hown

theorem wp_PackageInitStart (pkg : GoString) (σ : GMap GoString Bool) :
    {{ ownGoState (GF := GF) σ }} (App (Val (GoInstruction (PackageInitStart pkg))) (Val #())) @ s; E
    {{ RET #(); ownGoState (<[pkg := false]> σ) }} := by
  iintro %Φ Hown HΦ
  iapply wp_GoInstruction' (s := s) (E := E) (PackageInitStart pkg) #() Φ
    (fun gs => ⟨_, _, rfl, rfl, rfl⟩)
  inext
  iintro %e' %gs %gs' %Hstep _ Hauth
  obtain ⟨-, rfl, rfl⟩ := Hstep
  icombine Hauth Hown gives %Heq
  subst Heq
  imod ownGoState_update _ _ (<[pkg := false]> gs) $$ Hown Hauth with ⟨Hown, Hauth⟩
  imodintro
  iframe Hauth
  iapply wp_value'
  iapply HΦ $$ Hown

theorem wp_PackageInitFinish (pkg : GoString) (σ : GMap GoString Bool) :
    {{ ownGoState (GF := GF) σ }} (App (Val (GoInstruction (PackageInitFinish pkg))) (Val #())) @ s; E
    {{ RET #(); ownGoState (<[pkg := true]> σ) }} := by
  iintro %Φ Hown HΦ
  iapply wp_GoInstruction' (s := s) (E := E) (PackageInitFinish pkg) #() Φ
    (fun gs => ⟨_, _, rfl, rfl, rfl⟩)
  inext
  iintro %e' %gs %gs' %Hstep _ Hauth
  obtain ⟨-, rfl, rfl⟩ := Hstep
  icombine Hauth Hown gives %Heq
  subst Heq
  imod ownGoState_update _ _ (<[pkg := true]> gs) $$ Hown Hauth with ⟨Hown, Hauth⟩
  imodintro
  iframe Hauth
  iapply wp_value'
  iapply HΦ $$ Hown

end go_wps

section go_wps2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
variable {s : Stuckness} {E : CoPset}

theorem wp_GlobalAlloc (v : GoString) (t : go.GoType) {V : Type} [ZeroVal V]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] :
    {{ (True : IProp GF) }} (App (Val (go.GlobalAlloc v t)) (Val #())) @ s; E
    {{ RET #(); globalAddr v ↦ zero_val V }} := by
  rw [go.GlobalAlloc_unseal]
  iintro %Φ _ HΦ
  wp_call
  wp_apply_core wp_alloc (zero_val V)
  iintro %l Hl
  wp_pures
  by_cases h : l = globalAddr v
  · subst h
    simp only [decide_true]
    wp_pures
    iapply HΦ $$ Hl
  · simp only [h, decide_false]
    wp_pures
    iapply wp_AngelicExit

end go_wps2

/-! ## Helper lemmas for establishing `IntoValTyped` -/

section mem_lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable {s : Stuckness} {E : CoPset}

theorem _internal_wp_untyped_read (l : Loc) (dq : DFrac) (v : val) :
    {{ ▷ heapPointsto (GF := GF) l dq v }} (App (Val Read) (Val #l)) @ s; E
    {{ RET v; heapPointsto l dq v }} := by
  iintro %Φ Hl HΦ
  wp_call
  wp_apply_core wp_start_read l dq v $$ Hl
  iintro ⟨Hst, Hrest⟩
  wp_pures
  wp_apply_core wp_finish_read l dq v $$ [Hst Hrest]
  · iframe
  iintro Hl
  wp_pures
  iapply HΦ $$ Hl

theorem _internal_wp_untyped_store (l : Loc) (v v' : val) :
    {{ ▷ heapPointsto (GF := GF) l (.own 1) v }} (App (App (Val Store) (Val #l)) (Val v')) @ s; E
    {{ RET #(); heapPointsto l (.own 1) v' }} := by
  iintro %Φ Hl HΦ
  wp_call
  wp_apply_core wp_prepare_write l v $$ Hl
  iintro ⟨Hl, Hl'⟩
  wp_pures
  wp_apply_core wp_finish_store l v' v $$ [Hl Hl']
  · iframe
  iintro Hl
  iapply HΦ $$ Hl

end mem_lemmas

/-! ## Typed points-to instances for primitive types -/

noncomputable section typed_pointsto_instances
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
open ProofMode

instance typedPointsto_unit : TypedPointsto (GF := GF) Unit where
  typedPointstoDef l _ _ := iprop(⌜l ≠ null⌝)
  typedPointstoDef_dfractional _ _ := inferInstance
  typedPointstoDef_timeless _ _ _ := inferInstance
  typedPointsto_agree _ _ _ v1 v2 := by
    iintro _ _; ipureintro; cases v1; cases v2; rfl

/-- A typed points-to given by `heapPointsto l dq #v`, for `V` with an injective
`intoVal`. -/
def heapTypedPointsto (V : Type) (hinj : Function.Injective (intoVal (V := V))) :
    TypedPointsto (GF := GF) V where
  typedPointstoDef l v dq := heapPointsto l dq #v
  typedPointstoDef_dfractional l v := heapPointsto_dfractional l #v
  typedPointstoDef_timeless l v dq := heapPointsto_timeless l dq #v
  typedPointsto_agree l dq1 dq2 v1 v2 := by
    iintro H1 H2
    icombine H1 H2 gives % ⟨_, Heq⟩
    ipureintro; exact hinj Heq

theorem typedPointstoDef_heap (V : Type) (hinj : Function.Injective (intoVal (V := V)))
    (l : Loc) (v : V) (dq : DFrac) :
    @typedPointstoDef GF V (heapTypedPointsto V hinj) l v dq = heapPointsto l dq #v := rfl

instance typedPointsto_loc : TypedPointsto (GF := GF) Loc :=
  heapTypedPointsto Loc go.intoVal_inj
instance typedPointsto_w64 : TypedPointsto (GF := GF) w64 :=
  heapTypedPointsto w64 go.intoVal_inj
instance typedPointsto_w32 : TypedPointsto (GF := GF) w32 :=
  heapTypedPointsto w32 go.intoVal_inj
instance typedPointsto_w16 : TypedPointsto (GF := GF) w16 :=
  heapTypedPointsto w16 go.intoVal_inj
instance typedPointsto_w8 : TypedPointsto (GF := GF) w8 :=
  heapTypedPointsto w8 go.intoVal_inj
instance typedPointsto_bool : TypedPointsto (GF := GF) Bool :=
  heapTypedPointsto Bool go.intoVal_inj
instance typedPointsto_string : TypedPointsto (GF := GF) GoString :=
  heapTypedPointsto GoString go.intoVal_inj
instance typedPointsto_slice : TypedPointsto (GF := GF) slice.t :=
  heapTypedPointsto slice.t go.intoVal_inj
instance typedPointsto_interface : TypedPointsto (GF := GF) interface.t :=
  heapTypedPointsto interface.t go.intoVal_inj
instance typedPointsto_proph_id : TypedPointsto (GF := GF) proph_id :=
  heapTypedPointsto proph_id go.intoVal_inj

include hG in
theorem intoVal_inj_func : Function.Injective (intoVal (V := func.t)) := by
  intro f1 f2 h
  rw [go.intoVal_unfold func.t] at h
  cases f1; cases f2; cases h; rfl

instance typedPointsto_func : TypedPointsto (GF := GF) func.t :=
  heapTypedPointsto func.t (intoVal_inj_func (hG := hG))

end typed_pointsto_instances

/-! ## `IntoValTypedUnderlying` instances for primitive types -/

/-- Internal Go steps (`⤳[internal]`) as untagged steps. Used as a local
instance to prove `IntoValTyped` instances (Rocq: `pose proof (go.tagged_steps internal)`). -/
theorem go.tagged_internal_inst [FfiSyntax] [GoLocalContext] [GoGlobalContext]
    {instr : GoInstruction} {args : val} {e : Expr} [h : ⟦instr, args⟧ ⤳[internal] e] :
    ⟦instr, args⟧ ⤳ e :=
  h.isGoStep_det_internal

section into_val_typed_instances
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
open ProofMode

attribute [local instance] go.tagged_internal_inst

theorem heapPointsto_non_null_dup (l : Loc) (dq : DFrac) (v : val) :
    heapPointsto (GF := GF) l dq v ⊢ heapPointsto l dq v ∗ ⌜l ≠ null⌝ := by
  unfold heapPointsto
  iintro ⟨%Hl, H⟩
  iframe H
  isplit <;> ipureintro <;> exact Hl

/-- Prove `IntoValTypedUnderlying V t` for a type whose typed points-to is
`heapPointsto l dq #v` and which is allocated, loaded and stored with the
untyped primitives (Rocq `solve_into_val_typed`). -/
macro "solve_into_val_typed" : tactic => `(tactic| (
  constructor
  all_goals try simp only [typedPointsto_unseal, typedPointstoWrap, typedPointstoDef_heap]
  · intro s E t _ v
    iintro %Φ _ HΦ
    wp_pures
    wp_apply_core wp_alloc_untyped _
    iintro %l Hl
    icases heapPointsto_non_null_dup l _ _ $$ Hl with ⟨Hl, %Hnn⟩
    iapply HΦ
    iframe Hl
    ipureintro; exact Hnn
  · intro s E t _ l dq v
    iintro %Φ Hl HΦ
    icases Hl with ⟨Hl, %Hnn⟩
    wp_pures
    wp_apply_core _internal_wp_untyped_read l dq _ $$ Hl
    iintro Hl
    iapply HΦ
    iframe Hl
    ipureintro; exact Hnn
  · intro s E t _ l v w
    iintro %Φ Hl HΦ
    icases Hl with ⟨Hl, %Hnn⟩
    wp_pures
    wp_apply_core _internal_wp_untyped_store l _ _ $$ Hl
    iintro Hl
    iapply HΦ
    iframe Hl
    ipureintro; exact Hnn
  · infer_instance))

instance intoVal_typed_loc (t : go.GoType) :
    IntoValTypedUnderlying (GF := GF) Loc (go.PointerType t) := by
  solve_into_val_typed

instance intoVal_typed_func (sig : go.signature) :
    IntoValTypedUnderlying (GF := GF) func.t (go.FunctionType sig) := by
  solve_into_val_typed

instance intoVal_typed_slice (t : go.GoType) :
    IntoValTypedUnderlying (GF := GF) slice.t (go.SliceType t) := by
  solve_into_val_typed

instance intoVal_typed_interface (elems : List go.InterfaceElem) :
    IntoValTypedUnderlying (GF := GF) interface.t (go.InterfaceType elems) := by
  solve_into_val_typed

instance intoVal_typed_chan (t : go.GoType) (b : go.ChanDir) :
    IntoValTypedUnderlying (GF := GF) chan.t (go.ChannelType b t) := by
  solve_into_val_typed

instance intoVal_typed_map (k v : go.GoType) :
    IntoValTypedUnderlying (GF := GF) map.t (go.MapType k v) := by
  solve_into_val_typed

end into_val_typed_instances

/-! ## Struct points-to tactics -/

/-- Rocq `iStructNamed H`: split a typed points-to `H : l ↦{dq} v` for a struct
into its (named) field points-tos. -/
macro "iStructNamed " H:ident : tactic =>
  `(tactic| (
    icases typedPointsto_split _ _ _ $$ $H:ident with $H:ident
    try simp only [TypedPointsto.typedPointstoDef]
    iNamed $H:ident))
/-- Rocq `iStructNamedSuffix H "suf"`. -/
macro "iStructNamedSuffix " H:ident suff:str : tactic =>
  `(tactic| (
    icases typedPointsto_split _ _ _ $$ $H:ident with $H:ident
    try simp only [TypedPointsto.typedPointstoDef]
    iNamedSuffix $H:ident $suff))
/-- Rocq `iStructNamedPrefix H "pre"`. -/
macro "iStructNamedPrefix " H:ident pref:str : tactic =>
  `(tactic| (
    icases typedPointsto_split _ _ _ $$ $H:ident with $H:ident
    try simp only [TypedPointsto.typedPointstoDef]
    iNamedPrefix $H:ident $pref))

theorem typedPointsto_not_null_dup [FfiSyntax] {GF : BundledGFunctors} {V : Type}
    [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (dq : DFrac) :
    typedPointsto (GF := GF) l v dq ⊢ typedPointsto l v dq ∗ ⌜l ≠ null⌝ := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  iintro ⟨H, %h⟩
  iframe H
  isplit <;> ipureintro <;> exact h

/-- Prove `typedPointstoDef_dfractional` for a struct (Rocq: solved by `Program`). -/
macro "solve_typed_pointsto_dfractional" : tactic =>
  `(tactic| (intros; simp only [named]; infer_instance))

/-- Prove `typedPointstoDef_timeless` for a struct (Rocq: solved by `Program`). -/
macro "solve_typed_pointsto_timeless" : tactic =>
  `(tactic| (intros; simp only [named]; infer_instance))

/-- Rocq `solve_typed_pointsto_agree`: prove `typedPointsto_agree` for a
struct whose typed points-to is the conjunction of its field points-tos. -/
macro "solve_typed_pointsto_agree" : tactic => `(tactic| (
  intro l dq1 dq2 v1 v2
  cases v1; cases v2
  simp only [named]
  iintro H1 H2
  repeat (icases H1 with ⟨Hf, H1⟩; icases H2 with ⟨Hf', H2⟩; icombine Hf Hf' gives %Heq;
          subst Heq)
  ipureintro; first | rfl | trivial))

section tactics
open Lean Qq Iris.ProofMode

/-- All hypotheses of `hyps`: `(name, ivar, p, ty)`. (A helper of the tactics of
`Mem.lean`, `Pkg.lean` and `Auto.lean`.) -/
def hypsList {u} {prop : Q(Type u)} {bi : Q(BI $prop)} :
    ∀ {e}, Hyps bi e → List (Name × IVarId × Q(Bool) × Q($prop))
  | _, .emp _ => []
  | _, .hyp _ name ivar p ty _ => [(name, ivar, p, ty)]
  | _, .sep _ _ _ _ lhs rhs => hypsList rhs ++ hypsList lhs

end tactics

end Perennial
