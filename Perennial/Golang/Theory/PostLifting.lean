/-
The typed points-to `l ↦{dq} v`,
the classes `TypedPointsto`, `IntoValTypedUnderlying` and `IntoValTyped`, WPs
for basic Go instructions, and the typed points-to instances for primitive
types.

Notes:
* There is no `Countable` instance for interfaces: `gmap` only needs
  `DecidableEq`.
* `go.NotNamed t`/`go.NotInterface t` are proved by one instance per
  constructor of `go.GoType`. A type
  hidden behind a (non-reducible) definition is therefore not seen through; make
  such definitions `@[reducible]` (or state the instance).
* `IntoValTyped.wp_load` is not exported (it would clash with the untyped
  `Perennial.wp_load` of `GooseLang/Lifting.lean`);
  write `IntoValTyped.wp_load`. `wp_alloc` and `wp_store` are exported.
* The typed points-to notation is `l ↦{dq} v`, `l ↦ v` (full ownership) and
  `l ↦□ v` (discarded), scoped to `Perennial`.
-/
module

public import Perennial.Golang.Theory.ProofMode
public import Perennial.Golang.Theory.Display
public import Perennial.Golang.Defn.Pre
public import Perennial.Helpers.NamedProps
public import Perennial.IrisLib.DFractional
public import Perennial.Golang.Theory.RawCells

@[expose] public section

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
    rw [go.intoVal_unfold GoFunc]
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
`TypeRepr t V` instance (with the binder `[ZeroVal V]` first, typeclass search
gets stuck on `ZeroVal ?V`). -/
instance (priority := high) go_zero_val_step' [FfiSyntax] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] [go.CoreSemantics] {V : Type} {zv : ZeroVal V} {t : go.GoType}
    [TypeRepr t V] : ⟦GoZeroVal t, #()⟧ ⤳ #(zero_val V) :=
  go.go_zero_val_step

/-- `go.structFieldRef_step` with the `ZeroVal V` instance determined by
`TypeRepr t V` (see `go_zero_val_step'`). -/
instance (priority := high) structFieldRef_step' [FfiSyntax] [GoLocalContext]
    [GoGlobalContext] [GoSemanticsFunctions] [go.CoreSemantics] (t : go.GoType) (f : GoString)
    (l : Loc) {V : Type} {zv : ZeroVal V} [TypeRepr t V] :
    ⟦StructFieldRef t f, #l⟧ ⤳[under]
      (if l = null then Panic "nil pointer dereference" else #(structFieldRef V f l)) :=
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

/-- A field address is `null` exactly when the struct's address is
(`go.structFieldRef_null`, `go.structFieldRef_null_inv`). -/
@[simp] theorem structFieldRef_eq_null_iff [FfiSyntax] [GoSemanticsFunctions] [GoLocalContext]
    [GoGlobalContext] [go.CoreSemantics] {V' : Type} {f : GoString} {l : Loc} :
    structFieldRef V' f l = null ↔ l = null :=
  ⟨go.structFieldRef_null_inv V' f l, by rintro rfl; exact go.structFieldRef_null V' f⟩

instance locNonNullFrom_field_left [FfiSyntax] [GoSemanticsFunctions] [GoLocalContext]
    [GoGlobalContext] [go.CoreSemantics] {V' : Type} {f : GoString}
    {loc l : Loc} [h : LocNonNullFrom loc l] : LocNonNullFrom (structFieldRef V' f loc) l :=
  ⟨fun hn => h.ne_null (fun e => hn (structFieldRef_eq_null_iff.2 e))⟩

instance locNonNullFrom_field_right [FfiSyntax] [GoSemanticsFunctions] [GoLocalContext]
    [GoGlobalContext] [go.CoreSemantics] {V' : Type} {f : GoString}
    {loc l : Loc} [h : LocNonNullFrom loc l] : LocNonNullFrom loc (structFieldRef V' f l) :=
  ⟨fun hn e => h.ne_null hn (structFieldRef_eq_null_iff.1 e)⟩

/-- A points-to at `loc` shows `l ≠ null` when `loc` and `l` are field addresses of a
common base (`LocNonNullFrom`): `wp_auto`
and `wp_pures` use it for the side condition of a field reference
(`pure_wp_structFieldRef`). -/
instance typedPointsto_hypPure (loc l : Loc) (v : V) (dq : DFrac) [h : LocNonNullFrom loc l] :
    HypPure (typedPointsto (GF := GF) loc v dq) (l ≠ null) :=
  ⟨(typedPointsto_not_null loc v dq).trans (pure_mono h.ne_null)⟩

end typed_pointsto_props

/-! ## `IntoValTyped` -/

section into_val_defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- A fresh allocation of a value of representation `V` at `l`: in a real block, at an
offset aligned to `typeAlign V` (`IsFreshAligned`). -/
def AllocAligned [GoSemanticsFunctions] (V : Type) (l : Loc) : Prop :=
  l.locCar ≠ 0 ∧ typeAlign V ∣ l.locOff

/-- `IntoValTypedUnderlying V t_under` provides proofs that allocating, loading
and storing at any type `t` with underlying type `t_under` respects the typed
points-to for `V`. -/
class IntoValTypedUnderlying (V : outParam Type) (t_under : go.GoType) [ZeroVal V]
    [TypedPointsto (GF := GF) V] [GoSemanticsFunctions] : Prop where
  wp_alloc_def : ∀ {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u t_under] (v : V),
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoAlloc t))) (Val #v)) @ s; E
    {{ (l : Loc), RET #l; l ↦ v ∗ ⌜AllocAligned V l⌝ }}
  wp_load_def : ∀ {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u t_under] (l : Loc)
      (dq : DFrac) (v : V),
    {{ (l ↦{dq} v : IProp GF) }} (App (Val (GoInstruction (GoLoad t))) (Val #l)) @ s; E
    {{ RET #v; l ↦{dq} v }}
  wp_store_def : ∀ {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u t_under] (l : Loc)
      (v w : V),
    {{ (l ↦ v : IProp GF) }} (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w))) @ s; E
    {{ RET #(); l ↦ w }}
  /-- A store into the `typeSize V` cells at `l`, whatever they hold, makes `l ↦ w`: how a
  fresh allocation (`AllocN`) is initialized. -/
  wp_store_raw_def : ∀ {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u t_under] (l : Loc)
      (w : V),
    {{ (⌜l.locCar ≠ 0⌝ ∗ rawCells l (typeSize V) : IProp GF) }}
      (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w))) @ s; E
    {{ RET #(); l ↦ w }}
  type_repr_def : go.TypeReprUnderlying t_under V

/-- `IntoValTyped V t`: allocating, loading and storing at Go type `t` respects
the typed points-to for `V`. -/
class IntoValTyped (V : outParam Type) (t : go.GoType) [ZeroVal V] [TypedPointsto (GF := GF) V]
    [GoSemanticsFunctions] : Prop where
  /-- An allocation is aligned to its type's alignment (`IsFreshAligned`): what Go
  promises a variable. -/
  wp_alloc : ∀ {s : Stuckness} {E : CoPset} (v : V),
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoAlloc t))) (Val #v)) @ s; E
    {{ (l : Loc), RET #l; l ↦ v ∗ ⌜AllocAligned V l⌝ }}
  wp_load : ∀ {s : Stuckness} {E : CoPset} (l : Loc) (dq : DFrac) (v : V),
    {{ (l ↦{dq} v : IProp GF) }} (App (Val (GoInstruction (GoLoad t))) (Val #l)) @ s; E
    {{ RET #v; l ↦{dq} v }}
  wp_store : ∀ {s : Stuckness} {E : CoPset} (l : Loc) (v w : V),
    {{ (l ↦ v : IProp GF) }} (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w))) @ s; E
    {{ RET #(); l ↦ w }}
  wp_store_raw : ∀ {s : Stuckness} {E : CoPset} (l : Loc) (w : V),
    {{ (⌜l.locCar ≠ 0⌝ ∗ rawCells l (typeSize V) : IProp GF) }}
      (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w))) @ s; E
    {{ RET #(); l ↦ w }}
  [type_repr : TypeRepr t V]

attribute [instance] IntoValTyped.type_repr
export IntoValTyped (wp_alloc wp_store wp_store_raw)

instance underlying_to_into_val_typed {V : Type} {t_under : go.GoType} {zv : ZeroVal V}
    {tp : TypedPointsto (GF := GF) V} [GoSemanticsFunctions] [go.PreSemantics] {t : go.GoType}
    [t ↓u t_under] [h : IntoValTypedUnderlying (GF := GF) V t_under] :
    IntoValTyped (GF := GF) V t where
  wp_alloc v := h.wp_alloc_def v
  wp_load l dq v := h.wp_load_def l dq v
  wp_store l v w := h.wp_store_def l v w
  wp_store_raw l w := h.wp_store_raw_def l w
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

/-- `StructFieldRef t f #l` steps to the field address when `l ≠ null`; on
`null` it is a stuck run-time panic (`go.structFieldRef_step`). `wp_auto` and
`wp_pures` discharge the side condition from a Lean hypothesis `l' ≠ null`, or
from a hypothesis of the context with `HypPure` (a points-to, `isMutex`,
`isSema`, ... at an address with the same base as `l`: `LocNonNullFrom`), which
they then keep as a local `Hφ : l ≠ null`. -/
instance (priority := high) pure_wp_structFieldRef (t : go.GoType) (f : GoString) (l r : Loc)
    (msg : String)
    [h : go.IsGoStepPureDet (StructFieldRef t f) #l (if l = null then Panic msg else Val #r)] :
    PureWp (G := G) (L := L) (l ≠ null) (App (Val (GoInstruction (StructFieldRef t f))) (Val #l))
      (Val #r) where
  pure_wp_wp s E Φ K hnn := by
    have := (pure_wp_go_step_det (G := G) (L := L) _ _ _ (h := h)).pure_wp_wp s E Φ K trivial
    simp only [hnn, ↓reduceIte] at this
    exact this

/-- (Time receipts) A deterministic pure Go instruction step
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

theorem rawCells_of_pointstoVals (l : Loc) (n : Nat) :
    pointstoVals l (DFrac.own 1) (List.replicate n (LitV LitPad)) ⊢
      (rawCells l (n : Int) : IProp GF) := by
  unfold pointstoVals rawCells
  rw [show ((n : Int)).toNat = n by omega]
  induction n generalizing l with
  | zero => iintro _; rw [List.range_zero]; iapply BigSepL.bigSepL_nil.2; itrivial
  | succ n ih =>
    rw [List.replicate_succ, List.range_succ_eq_map]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H0, H⟩
    iapply BigSepL.bigSepL_cons.2
    simp only [Int.natCast_zero, loc_add_0]
    isplitl [H0]
    · iexact H0
    rw [BigSepL.bigSepL_map]
    simp only [loc_add_succ]
    iapply ih (l +ₗ 1) $$ H

/-- Raw cells are pads. -/
theorem rawCells_vals (l : Loc) (n : Nat) :
    rawCells l (n : Int) ⊢
      (pointstoVals l (DFrac.own 1) (List.replicate n (LitV LitPad)) : IProp GF) := by
  unfold rawCells pointstoVals
  rw [show ((n : Int)).toNat = n by omega]
  induction n generalizing l with
  | zero =>
    iintro _; rw [List.replicate_zero]; iapply BigSepL.bigSepL_nil.2; itrivial
  | succ n ih =>
    rw [List.range_succ_eq_map, List.replicate_succ]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H0, H⟩
    rw [BigSepL.bigSepL_map]
    simp only [loc_add_succ]
    ihave H := ih (l +ₗ 1) $$ H
    iapply BigSepL.bigSepL_cons.2
    simp only [Int.natCast_zero, loc_add_0, loc_add_succ]
    iframe H0
    iexact H

/-- Pads may be overwritten by any store. -/
theorem writeCompat_pads (enc : Encoding) (n : Nat) :
    WriteCompat enc (List.replicate n (LitV LitPad)) := by
  cases enc <;> simp [WriteCompat, List.mem_replicate] <;> intros <;> simp_all

/-- The cells of an encoded value may be overwritten by a store of the same encoding. -/
theorem encode_writeCompat {enc : Encoding} {v : val} {vs : List val}
    (h : encode enc v = some vs) : WriteCompat enc vs := by
  cases enc with
  | word n =>
    simp only [encode, Option.map_eq_some_iff] at h
    obtain ⟨z, -, rfl⟩ := h
    simp only [WriteCompat, List.mem_map]
    rintro _ ⟨b, -, rfl⟩; exact .inl ⟨b, rfl⟩
  | cell k =>
    simp only [encode] at h
    split at h
    · rename_i hk; cases h
      simp only [WriteCompat, List.mem_cons, List.mem_replicate]
      rintro w (rfl | ⟨-, rfl⟩) b hb
      · subst hb; exact absurd hk.2.1 (by simp [byteOf?])
      · cases hb
    · cases h

theorem pointstoVals_non_null (l : Loc) (q : DFrac) (vs : List val) (hne : vs ≠ []) :
    pointstoVals l q vs ⊢ (pointstoVals l q vs ∗ ⌜l.locCar ≠ 0⌝ : IProp GF) := by
  iintro H
  icases pointstoVals_split' l q vs hne $$ H with ⟨%hc, H⟩
  isplitl [H]
  · iapply pointstoVals_of_na l q vs hc $$ H
  · ipureintro; exact hc

theorem uint_nat_W64 (n : Nat) (h : n < 2 ^ 64) : uint.nat (W64 (n : Int)) = n := by
  simp only [uint.nat, W64, BitVec.toNat_ofInt]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega

theorem uint_nat_W64' (a : Int) (h1 : 1 ≤ a) (h2 : a ≤ 8) : ((uint.nat (W64 a) : Nat) : Int) = a := by
  simp only [uint.nat, W64, BitVec.toNat_ofInt]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega

/-- The non-atomic load of an encoded value (`ReadN`). -/
theorem wp_ReadN (enc : Encoding) (l : Loc) (dq : DFrac) (vs : List val) (v : val)
    (hlen : vs.length = enc.size) (hdec : decode enc vs = some v) :
    {{ ▷ pointstoVals (GF := GF) l dq vs }} (App (Val (ReadN enc)) (Val #l)) @ s; E
    {{ RET v; pointstoVals l dq vs }} := by
  iintro %Φ Hl HΦ
  wp_call
  wp_apply_core wp_start_readN enc l dq vs v hlen hdec $$ Hl
  iintro Hr
  wp_pures
  wp_apply_core wp_finish_readN enc l dq vs hlen $$ Hr
  iintro Hl
  wp_pures
  iapply HΦ $$ Hl

/-- The non-atomic store of an encoded value (`StoreN`), over cells it may overwrite
(`WriteCompat`). -/
theorem wp_StoreN (enc : Encoding) (l : Loc) (vs vs' : List val) (v : val)
    (hlen : vs.length = enc.size) (hne : vs ≠ []) (hcompat : WriteCompat enc vs)
    (henc : encode enc v = some vs') :
    {{ ▷ pointstoVals (GF := GF) l (DFrac.own 1) vs }}
      (App (App (Val (StoreN enc)) (Val #l)) (Val v)) @ s; E
    {{ RET #(); pointstoVals l (DFrac.own 1) vs' }} := by
  iintro %Φ Hl HΦ
  wp_call
  wp_apply_core wp_prepare_writeN enc l vs hlen hne hcompat $$ Hl
  iintro Hw
  wp_pures
  wp_apply_core wp_finish_storeN enc l vs vs' v hlen henc $$ Hw
  iintro Hl
  iapply HΦ $$ Hl

/-- The allocation of an encoded value (`allocEncoded`). -/
theorem wp_allocEncoded (enc : Encoding) (v : val) (vs : List val) (hpos : 1 ≤ enc.size)
    (hsize : enc.size < 2 ^ 63) (henc : encode enc v = some vs) :
    {{ (True : IProp GF) }} (go.allocEncoded enc v) @ s; E
    {{ (l : Loc), RET #l; ⌜l.locCar ≠ 0 ∧ (enc.align : Int) ∣ l.locOff⌝ ∗
        pointstoVals l (DFrac.own 1) vs }} := by
  iintro %Φ _ HΦ
  have halign : enc.align < 2 ^ 64 := by cases enc <;> simp [Encoding.align, Encoding.size] at * <;> omega
  unfold go.allocEncoded
  wp_apply_core wp_allocN _ _ _
  iintro %l ⟨%Hoff, Hl⟩
  rw [uint_nat_W64 _ (by omega)]
  wp_pures
  wp_apply_core wp_StoreN enc l _ vs v (by simp) (by simp; omega) (writeCompat_pads _ _)
    henc $$ Hl
  iintro Hl
  wp_pures
  iapply HΦ
  iframe Hl
  ipureintro; refine ⟨Hoff.1, ?_⟩
  have := Hoff.2
  rwa [uint_nat_W64 _ halign] at this

/-- Allocating `sz` cells (`AllocN`) and storing into them: what `GoAlloc` of a struct or
an array expands to. -/
theorem wp_alloc_raw (t : go.GoType) (sz al : Int) (hsz : 0 ≤ sz ∧ sz < 2^63)
    (hal : 0 ≤ al ∧ al ≤ 8) (v : val) (P : Loc → IProp GF)
    (hstore : ∀ l, {{ (⌜l.locCar ≠ 0⌝ ∗ rawCells l sz : IProp GF) }}
      (App (Val (GoInstruction (GoStore t))) (Val (PairV #l v))) @ s; E
      {{ RET #(); P l }}) :
    {{ (True : IProp GF) }}
      (Let "l" (AllocN (Val (PairV (LitV (LitInt (W64 sz))) (LitV (LitInt (W64 al)))))
          (Val (LitV LitPad)))
        gl(GoStore t ("l", v) ;; "l")) @ s; E
    {{ (l : Loc), RET #l; P l ∗ ⌜l.locCar ≠ 0 ∧ al ∣ l.locOff⌝ }} := by
  iintro %Φ _ HΦ
  wp_apply_core wp_allocN _ _ _
  iintro %l ⟨%Hoff, Hpts⟩
  have hn : ((uint.nat (W64 sz) : Nat) : Int) = sz := by
    simp only [uint.nat, W64, BitVec.toNat_ofInt]
    rw [Int.emod_eq_of_lt hsz.1 (by omega)]; omega
  have hc := Hoff.1
  rw [show uint.nat (W64 sz) = sz.toNat by
    simp only [uint.nat, W64, BitVec.toNat_ofInt]
    rw [Int.emod_eq_of_lt hsz.1 (by omega)]]
  ihave Hraw := rawCells_of_pointstoVals l _ $$ Hpts
  rw [show ((sz.toNat : Nat) : Int) = sz by omega]
  wp_pures
  wp_apply_core hstore l $$ [Hraw]
  · iframe; ipureintro; exact hc
  iintro HP
  wp_pures
  iapply HΦ
  iframe HP
  ipureintro
  refine ⟨hc, ?_⟩
  have := Hoff.2
  rwa [show ((uint.nat (W64 al) : Nat) : Int) = al by
    simp only [uint.nat, W64, BitVec.toNat_ofInt]
    rw [Int.emod_eq_of_lt hal.1 (by omega)]; omega] at this

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
  iintro %l ⟨Hl, -⟩
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

theorem pointstoVals_agree (l : Loc) (dq1 dq2 : DFrac) (vs1 vs2 : List val)
    (hlen : vs1.length = vs2.length) :
    pointstoVals (GF := GF) l dq1 vs1 ∗ pointstoVals l dq2 vs2 ⊢ ⌜vs1 = vs2⌝ := by
  induction vs1 generalizing l vs2 with
  | nil => cases vs2 with
    | nil => iintro _; ipureintro; rfl
    | cons => simp at hlen
  | cons v vs1 ih =>
    cases vs2 with
    | nil => simp at hlen
    | cons w vs2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      unfold pointstoVals
      iintro ⟨H1, H2⟩
      icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨Hv, H1⟩
      icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨Hw, H2⟩
      icases heapPointsto_agree _ _ _ _ _ $$ [Hv Hw] with %Hvw
      · iframe
      have Hk : ∀ k : Nat, l +ₗ ((k + 1 : Nat) : Int) = l +ₗ 1 +ₗ (k : Int) := by
        intro k; rw [loc_add_assoc]; congr 1; omega
      simp only [Hk]
      icases ih (l +ₗ 1) vs2 hlen $$ [H1 H2] with %Hrest
      · unfold pointstoVals; iframe
      ipureintro; rw [Hvw, Hrest]

theorem byteVals_inj (bs1 bs2 : List w8) (h : byteVals bs1 = byteVals bs2) : bs1 = bs2 := by
  unfold byteVals at h
  induction bs1 generalizing bs2 with
  | nil => cases bs2 with
    | nil => rfl
    | cons => simp at h
  | cons b bs1 ih =>
    cases bs2 with
    | nil => simp at h
    | cons c bs2 =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      injection h1 with h1; injection h1 with h1
      rw [h1, ih bs2 h2]

/-- The typed points-to of a type whose values have encoding `enc`: the cells of the
value's encoding (`encodeVals`). -/
def encTypedPointsto (V : Type) (enc : Encoding) (hinj : Function.Injective (intoVal (V := V)))
    (henc : ∀ v : V, ∃ vs, encode enc #v = some vs) :
    TypedPointsto (GF := GF) V where
  typedPointstoDef l v dq := pointstoVals l dq (encodeVals enc #v)
  typedPointstoDef_dfractional l v := by unfold pointstoVals; infer_instance
  typedPointstoDef_timeless l v dq := by unfold pointstoVals; infer_instance
  typedPointsto_agree l dq1 dq2 v1 v2 := by
    obtain ⟨vs1, h1⟩ := henc v1
    obtain ⟨vs2, h2⟩ := henc v2
    rw [encodeVals_eq h1, encodeVals_eq h2]
    iintro H1 H2
    icases pointstoVals_agree l dq1 dq2 vs1 vs2
      (by rw [encode_length h1, encode_length h2]) $$ [H1 H2] with %h
    · iframe
    ipureintro
    subst h
    have e := (decode_encode h1).symm.trans (decode_encode h2)
    exact hinj (Option.some.inj e)

theorem typedPointstoDef_enc (V : Type) (enc : Encoding) (hinj : Function.Injective (intoVal (V := V)))
    (henc : ∀ v : V, ∃ vs, encode enc #v = some vs) (l : Loc) (v : V) (dq : DFrac) :
    @typedPointstoDef GF V (encTypedPointsto V enc hinj henc) l v dq =
      pointstoVals l dq (encodeVals enc #v) := rfl

theorem typedPointstoDef_enc_iff (V : Type) (enc : Encoding)
    (hinj : Function.Injective (intoVal (V := V))) (henc : ∀ v : V, ∃ vs, encode enc #v = some vs)
    (l : Loc) (v : V) (dq : DFrac) :
    @typedPointstoDef GF V (encTypedPointsto V enc hinj henc) l v dq ⊣⊢
      pointstoVals l dq (encodeVals enc #v) := .rfl

/-- The representation types whose values are cell heads (`GoGlobalContext.intoVal_head_loc`,
...), so that they have a cell encoding. -/
class CellHeadType [GoGlobalContext] (V : Type) : Prop where
  head : ∀ v : V, IsCellHead (intoVal v)

instance [GoGlobalContext] : CellHeadType Loc := ⟨GoGlobalContext.intoVal_head_loc⟩
instance [GoGlobalContext] : CellHeadType Bool := ⟨GoGlobalContext.intoVal_head_bool⟩
instance [GoGlobalContext] : CellHeadType proph_id := ⟨GoGlobalContext.intoVal_head_proph_id⟩
instance [GoGlobalContext] : CellHeadType GoString := ⟨GoGlobalContext.intoVal_head_string⟩
instance [GoGlobalContext] : CellHeadType GoSlice := ⟨GoGlobalContext.intoVal_head_slice⟩
instance [GoGlobalContext] : CellHeadType GoFunc := ⟨GoGlobalContext.intoVal_head_func⟩
instance [GoGlobalContext] : CellHeadType GoInterface := ⟨GoGlobalContext.intoVal_head_interface⟩

theorem encode_cell (k : Nat) (hk : 1 ≤ k) {V : Type} [CellHeadType V] (v : V) :
    ∃ vs, encode (.cell k) #v = some vs :=
  ⟨#v :: List.replicate (k - 1) (LitV LitTail), by simp [encode, hk, CellHeadType.head v]⟩

include hG in
theorem encode_w64 (v : w64) : ∃ vs, encode (.word 8) #v = some vs := by
  rw [go.intoVal_unfold w64]; exact ⟨_, rfl⟩
include hG in
theorem encode_w32 (v : w32) : ∃ vs, encode (.word 4) #v = some vs := by
  rw [go.intoVal_unfold w32]; exact ⟨_, rfl⟩
include hG in
theorem encode_w16 (v : w16) : ∃ vs, encode (.word 2) #v = some vs := by
  rw [go.intoVal_unfold w16]; exact ⟨_, rfl⟩
include hG in
theorem encode_w8 (v : w8) : ∃ vs, encode (.word 1) #v = some vs := by
  rw [go.intoVal_unfold w8]; exact ⟨_, rfl⟩

instance typedPointsto_loc : TypedPointsto (GF := GF) Loc :=
  encTypedPointsto Loc (.cell 8) go.intoVal_inj (fun v => encode_cell 8 (by decide) v)
/-- An integer is its little-endian bytes. -/
instance typedPointsto_w64 : TypedPointsto (GF := GF) w64 :=
  encTypedPointsto w64 (.word 8) go.intoVal_inj (encode_w64 (hG := hG))
instance typedPointsto_w32 : TypedPointsto (GF := GF) w32 :=
  encTypedPointsto w32 (.word 4) go.intoVal_inj (encode_w32 (hG := hG))
instance typedPointsto_w16 : TypedPointsto (GF := GF) w16 :=
  encTypedPointsto w16 (.word 2) go.intoVal_inj (encode_w16 (hG := hG))
instance typedPointsto_w8 : TypedPointsto (GF := GF) w8 :=
  encTypedPointsto w8 (.word 1) go.intoVal_inj (encode_w8 (hG := hG))
/-- A `bool` is one cell (`Encoding.cell 1`), its `heapPointsto`. -/
instance typedPointsto_bool : TypedPointsto (GF := GF) Bool :=
  heapTypedPointsto Bool go.intoVal_inj
instance typedPointsto_string : TypedPointsto (GF := GF) GoString :=
  encTypedPointsto GoString (.cell 16) go.intoVal_inj (fun v => encode_cell 16 (by decide) v)
instance typedPointsto_slice : TypedPointsto (GF := GF) GoSlice :=
  encTypedPointsto GoSlice (.cell 24) go.intoVal_inj (fun v => encode_cell 24 (by decide) v)
instance typedPointsto_interface : TypedPointsto (GF := GF) GoInterface :=
  encTypedPointsto GoInterface (.cell 16) go.intoVal_inj (fun v => encode_cell 16 (by decide) v)
instance typedPointsto_proph_id : TypedPointsto (GF := GF) proph_id :=
  encTypedPointsto proph_id (.cell 8) go.intoVal_inj (fun v => encode_cell 8 (by decide) v)

include hG in
theorem intoVal_inj_func : Function.Injective (intoVal (V := GoFunc)) := by
  intro f1 f2 h
  rw [go.intoVal_unfold GoFunc] at h
  cases f1; cases f2; cases h; rfl

instance typedPointsto_func : TypedPointsto (GF := GF) GoFunc :=
  encTypedPointsto GoFunc (.cell 8) (intoVal_inj_func (hG := hG)) (fun v => encode_cell 8 (by decide) v)

/-- A one-cell points-to is a heap points-to. -/
theorem pointstoVals_single (l : Loc) (dq : DFrac) (v : val) :
    pointstoVals (GF := GF) l dq [v] ⊣⊢ (heapPointsto l dq v : IProp GF) := by
  unfold pointstoVals
  constructor
  · iintro H
    icases BigSepL.bigSepL_singleton.1 $$ H with H
    rw [show l +ₗ ((0 : Nat) : Int) = l by simp]
    iexact H
  · iintro H
    iapply BigSepL.bigSepL_singleton.2
    rw [show l +ₗ ((0 : Nat) : Int) = l by simp]
    iexact H

include hG in
theorem encodeVals_byte (v : w8) : encodeVals (.word 1) #v = [ (#v : val) ] := by
  rw [go.intoVal_unfold w8]
  show [LitV (LitByte (BitVec.ofInt 8 (v.toNat : Int)))] = [LitV (LitByte v)]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A byte's typed points-to is its cell. -/
theorem typedPointstoDef_w8 (l : Loc) (v : w8) (dq : DFrac) :
    @typedPointstoDef GF w8 typedPointsto_w8 l v dq ⊣⊢ heapPointsto l dq #v := by
  show pointstoVals l dq (encodeVals (.word 1) #v) ⊣⊢ _
  rw [encodeVals_byte (hG := hG)]
  exact pointstoVals_single l dq _

end typed_pointsto_instances


/-! ## `IntoValTypedUnderlying` instances for primitive types -/

/-- Internal Go steps (`⤳[internal]`) as untagged steps. Used as a local
instance to prove `IntoValTyped` instances. -/
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
  isplit <;> ipureintro
  · exact Hl
  · intro h; subst h; exact Hl rfl

theorem encode_ne_nil {enc : Encoding} {v : val} {vs : List val} (h : encode enc v = some vs)
    (hpos : 1 ≤ enc.size) : vs ≠ [] := by
  intro e; have := encode_length h; rw [e] at this; simp at this; omega

theorem rawCells_vals' (l : Loc) (m : Int) (n : Nat) (h : m = n) :
    rawCells l m ⊢
      (pointstoVals l (DFrac.own 1) (List.replicate n (LitV LitPad)) : IProp GF) := by
  subst h; exact rawCells_vals l n

/-- Prove `IntoValTypedUnderlying V t` for a type whose typed points-to is the cells of its
encoding `enc` (`hdef`) and which is allocated, loaded and stored as an encoded value
(`allocEncoded`, `ReadN`, `StoreN`). `henc` shows every value has an encoding, `hsize`
that `typeSize V` is its size. -/
macro "solve_into_val_typed'" enc:term:max henc:term:max hsize:term:max halign:term:max
    hdef:term:max :
    tactic => `(tactic| (
  constructor
  all_goals try simp only [typedPointsto_unseal, typedPointstoWrap]
  · intro s E t _ v
    iintro %Φ _ HΦ
    wp_pures
    obtain ⟨vs, hvs⟩ := $henc v
    wp_apply_core wp_allocEncoded $enc _ vs (by decide) (by decide) hvs
    iintro %l ⟨%Hc, Hl⟩
    iapply HΦ
    isplitl [Hl]
    · isplitl [Hl]
      · iapply ($hdef l v _).2; rw [encodeVals_eq hvs]; iexact Hl
      ipureintro; intro h; subst h; exact Hc.1 rfl
    ipureintro; refine ⟨Hc.1, ?_⟩; rw [show typeAlign _ = _ from $halign]
    simpa [Encoding.align] using Hc.2
  · intro s E t _ l dq v
    iintro %Φ Hl HΦ
    icases Hl with ⟨Hl, %Hnn⟩
    ihave Hl := ($hdef l v dq).1 $$ Hl
    wp_pures
    obtain ⟨vs, hvs⟩ := $henc v
    rw [encodeVals_eq hvs]
    wp_apply_core wp_ReadN $enc l dq vs _ (encode_length hvs) (decode_encode hvs) $$ Hl
    iintro Hl
    iapply HΦ
    isplitl [Hl]
    · iapply ($hdef l v dq).2; rw [encodeVals_eq hvs]; iexact Hl
    ipureintro; exact Hnn
  · intro s E t _ l v w
    iintro %Φ Hl HΦ
    icases Hl with ⟨Hl, %Hnn⟩
    ihave Hl := ($hdef l v _).1 $$ Hl
    wp_pures
    obtain ⟨vs, hvs⟩ := $henc v
    obtain ⟨ws, hws⟩ := $henc w
    rw [encodeVals_eq hvs]
    wp_apply_core wp_StoreN $enc l vs ws _ (encode_length hvs)
      (encode_ne_nil hvs (by decide)) (encode_writeCompat hvs) hws $$ Hl
    iintro Hl
    iapply HΦ
    isplitl [Hl]
    · iapply ($hdef l w _).2; rw [encodeVals_eq hws]; iexact Hl
    ipureintro; exact Hnn
  · intro s E t _ l w
    iintro %Φ ⟨%Hc, Hraw⟩ HΦ
    ihave Hl := rawCells_vals' l _ ($enc).size (($hsize).trans (by decide)) $$ Hraw
    wp_pures
    obtain ⟨ws, hws⟩ := $henc w
    wp_apply_core wp_StoreN $enc l _ ws _ (List.length_replicate ..)
      (by simp [Encoding.size]) (writeCompat_pads _ _) hws $$ Hl
    iintro Hl
    iapply HΦ
    isplitl [Hl]
    · iapply ($hdef l w _).2; rw [encodeVals_eq hws]; iexact Hl
    ipureintro; intro h; subst h; exact Hc rfl
  · infer_instance))

/-- `solve_into_val_typed'` for a typed points-to that is `encTypedPointsto V enc`. -/
macro "solve_into_val_typed" enc:term:max henc:term:max hsize:term:max halign:term:max :
    tactic =>
  `(tactic| solve_into_val_typed' $enc $henc $hsize $halign
    (fun l v dq => typedPointstoDef_enc_iff _ _ _ _ l v dq))

/-- The typed points-to of a `bool` is its cell (`Encoding.cell 1`). -/
theorem typedPointstoDef_bool (l : Loc) (v : Bool) (dq : DFrac) :
    @typedPointstoDef GF Bool typedPointsto_bool l v dq ⊣⊢
      pointstoVals l dq (encodeVals (.cell 1) #v) := by
  have h1 : encode (.cell 1) (#v : val) = some [ (#v : val) ] := by
    simp [encode, CellHeadType.head v]
  rw [encodeVals_eq h1,
    typedPointstoDef_heap]
  exact (pointstoVals_single l dq _).symm

instance intoVal_typed_loc (t : go.GoType) :
    IntoValTypedUnderlying (GF := GF) Loc (go.PointerType t) := by
  solve_into_val_typed (Encoding.cell 8) (fun v => encode_cell 8 (by decide) v) go.typeSize_loc go.typeAlign_loc

instance intoVal_typed_func (sig : go.signature) :
    IntoValTypedUnderlying (GF := GF) GoFunc (go.FunctionType sig) := by
  solve_into_val_typed (Encoding.cell 8) (fun v => encode_cell 8 (by decide) v) go.typeSize_func go.typeAlign_func

instance intoVal_typed_slice (t : go.GoType) :
    IntoValTypedUnderlying (GF := GF) GoSlice (go.SliceType t) := by
  solve_into_val_typed (Encoding.cell 24) (fun v => encode_cell 24 (by decide) v) go.typeSize_slice go.typeAlign_slice

instance intoVal_typed_interface (elems : List go.InterfaceElem) :
    IntoValTypedUnderlying (GF := GF) GoInterface (go.InterfaceType elems) := by
  solve_into_val_typed (Encoding.cell 16) (fun v => encode_cell 16 (by decide) v) go.typeSize_interface go.typeAlign_interface

instance intoVal_typed_chan (t : go.GoType) (b : go.ChanDir) :
    IntoValTypedUnderlying (GF := GF) GoChan (go.ChannelType b t) := by
  solve_into_val_typed (Encoding.cell 8) (fun v => encode_cell 8 (by decide) v) go.typeSize_loc go.typeAlign_loc

instance intoVal_typed_map (k v : go.GoType) :
    IntoValTypedUnderlying (GF := GF) GoMap (go.MapType k v) := by
  solve_into_val_typed (Encoding.cell 8) (fun v => encode_cell 8 (by decide) v) go.typeSize_loc go.typeAlign_loc

end into_val_typed_instances

/-! ## Struct points-to tactics -/

/-- `iStructNamed H`: split a typed points-to `H : l ↦{dq} v` for a struct
into its (named) field points-tos. -/
macro "iStructNamed " H:ident : tactic =>
  `(tactic| (
    icases typedPointsto_split _ _ _ $$ $H:ident with $H:ident
    try simp only [TypedPointsto.typedPointstoDef]
    iNamed $H:ident))
/-- `iStructNamedSuffix H "suf"`: `iStructNamed H`, adding the suffix `suf` to the names. -/
macro "iStructNamedSuffix " H:ident suff:str : tactic =>
  `(tactic| (
    icases typedPointsto_split _ _ _ $$ $H:ident with $H:ident
    try simp only [TypedPointsto.typedPointstoDef]
    iNamedSuffix $H:ident $suff))
/-- `iStructNamedPrefix H "pre"`: `iStructNamed H`, adding the prefix `pre` to the names. -/
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

/-- Prove `typedPointstoDef_dfractional` for a struct. -/
macro "solve_typed_pointsto_dfractional" : tactic =>
  `(tactic| (intros; simp only [named]; infer_instance))

/-- Prove `typedPointstoDef_timeless` for a struct. -/
macro "solve_typed_pointsto_timeless" : tactic =>
  `(tactic| (intros; simp only [named]; infer_instance))

/-- Prove `typedPointsto_agree` for a
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
