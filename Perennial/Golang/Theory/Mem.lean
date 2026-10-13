/-
Atomic WPs on typed points-to, the
`Access`/`AccessStrict` classes for accessing (struct field) points-to facts,
and the typed memory tactics `wp_load`, `wp_store`, `wp_alloc`,
`wp_alloc_auto`.

`Access`/`AccessStrict` are iris-lean `ipm_class`es, searched with the proof
mode's typeclass search (which can instantiate metavariables). The last two
parameters are `outParam`s.
-/
module

public import Perennial.Golang.Theory.PostLifting
public meta import Perennial.Golang.Theory.ProofMode
public meta import Perennial.Golang.Theory.PostLifting

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section goose_lang
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- The typed points-to of `V` is the cells of its values' encoding `enc` (the
`IntoValTyped` instances of the predeclared and primitive types). -/
class EncodedPointsto (V : Type) [TypedPointsto (GF := GF) V] (enc : outParam Encoding) : Prop where
  def_eq : ∀ l (v : V) dq,
    typedPointstoDef (GF := GF) l v dq ⊣⊢ pointstoVals l dq (encodeVals enc #v)
  encode_some : ∀ v : V, ∃ vs, encode enc #v = some vs
  inj : Function.Injective (intoVal (V := V))

/-! The atomic operations on a typed points-to of an encoded value (`typed.wp_atomic_load`,
…): they need the location to be aligned (`Aligned enc l`; for an integer, to its size),
and are stuck otherwise. -/
section atomic_wps
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {enc : Encoding}
variable [hE : EncodedPointsto (GF := GF) V enc]
variable {s : Stuckness} {E : CoPset}
open ProofMode

theorem typed.typedPointsto_encoded (l : Loc) (v : V) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊣⊢
      ∃ vs, ⌜encode enc #v = some vs⌝ ∗ ⌜l ≠ null⌝ ∗ pointstoVals l dq vs := by
  obtain ⟨vs, hvs⟩ := hE.encode_some v
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  constructor
  · iintro ⟨H, %Hnn⟩
    ihave H := (hE.def_eq l v dq).1 $$ H
    rw [encodeVals_eq hvs]
    iexists vs
    iframe H
    ipureintro; exact ⟨hvs, Hnn⟩
  · iintro ⟨%vs', %Hvs', %Hnn, H⟩
    rw [hvs] at Hvs'; cases Hvs'
    isplitl [H]
    · iapply (hE.def_eq l v dq).2; rw [encodeVals_eq hvs]; iexact H
    · ipureintro; exact Hnn

theorem typed.wp_atomic_load (l : Loc) (dq : DFrac) (v : V) (hal : Aligned enc l) :
    {{ ▷ (l ↦{dq} v : IProp GF) }} (LoadN enc (Val #l)) @ s; E {{ RET #v; l ↦{dq} v }} := by
  iintro %Φ Hl HΦ
  obtain ⟨vs, hvs⟩ := hE.encode_some v
  ihave Hl : ▷ (pointstoVals l dq vs ∗ ⌜l ≠ null⌝) $$ [Hl]
  · inext
    icases (typed.typedPointsto_encoded l v dq).1 $$ Hl with ⟨%vs', %Hvs', %Hnn, H⟩
    rw [hvs] at Hvs'; cases Hvs'
    iframe H; ipureintro; exact Hnn
  icases Hl with ⟨Hl, >%Hnn⟩
  iapply wp_loadN enc l dq vs #v hal (encode_length hvs) (decode_encode hvs) $$ Hl
  inext; iintro Hl
  iapply HΦ
  iapply (typed.typedPointsto_encoded l v dq).2
  iexists vs; iframe Hl; ipureintro; exact ⟨hvs, Hnn⟩

theorem typed.wp_atomic_swap (l : Loc) (v v' : V) (hal : Aligned enc l) :
    {{ ▷ (l ↦ v : IProp GF) }} (SwapN enc (Val #l) (Val #v')) @ s; E {{ RET #v; l ↦ v' }} := by
  iintro %Φ Hl HΦ
  obtain ⟨vs, hvs⟩ := hE.encode_some v
  obtain ⟨vs', hvs'⟩ := hE.encode_some v'
  ihave Hl : ▷ (pointstoVals l (DFrac.own 1) vs ∗ ⌜l ≠ null⌝) $$ [Hl]
  · inext
    icases (typed.typedPointsto_encoded l v _).1 $$ Hl with ⟨%vs'', %Hvs'', %Hnn, H⟩
    rw [hvs] at Hvs''; cases Hvs''
    iframe H; ipureintro; exact Hnn
  icases Hl with ⟨Hl, >%Hnn⟩
  iapply wp_swapN enc l vs vs' #v #v' hal (encode_length hvs) (decode_encode hvs) hvs' $$ Hl
  inext; iintro Hl
  iapply HΦ
  iapply (typed.typedPointsto_encoded l v' _).2
  iexists vs'; iframe Hl; ipureintro; exact ⟨hvs', Hnn⟩

theorem typed.wp_cmpxchg_fail (l : Loc) (v' v1 v2 : V) (dq : DFrac) (hal : Aligned enc l)
    (hne : v' ≠ v1) :
    {{ ▷ (l ↦{dq} v' : IProp GF) }} (CmpXchgN enc (Val #l) (Val (PairV #v1 #v2))) @ s; E
    {{ RET (PairV #v' #false); l ↦{dq} v' }} := by
  iintro %Φ Hl HΦ
  obtain ⟨vs, hvs⟩ := hE.encode_some v'
  ihave Hl : ▷ (pointstoVals l dq vs ∗ ⌜l ≠ null⌝) $$ [Hl]
  · inext
    icases (typed.typedPointsto_encoded l v' dq).1 $$ Hl with ⟨%vs'', %Hvs'', %Hnn, H⟩
    rw [hvs] at Hvs''; cases Hvs''
    iframe H; ipureintro; exact Hnn
  icases Hl with ⟨Hl, >%Hnn⟩
  iapply wp_cmpxchgN_fail enc l dq vs #v' #v1 #v2 hal (encode_length hvs) (decode_encode hvs)
    (fun h => hne (hE.inj h)) $$ Hl
  inext; iintro Hl
  iapply HΦ
  iapply (typed.typedPointsto_encoded l v' dq).2
  iexists vs; iframe Hl; ipureintro; exact ⟨hvs, Hnn⟩

theorem typed.wp_cmpxchg_suc (l : Loc) (v' v1 v2 : V) (hal : Aligned enc l) (heq : v' = v1) :
    {{ ▷ (l ↦ v' : IProp GF) }} (CmpXchgN enc (Val #l) (Val (PairV #v1 #v2))) @ s; E
    {{ RET (PairV #v' #true); l ↦ v2 }} := by
  iintro %Φ Hl HΦ
  obtain ⟨vs, hvs⟩ := hE.encode_some v'
  obtain ⟨vs2, hvs2⟩ := hE.encode_some v2
  ihave Hl : ▷ (pointstoVals l (DFrac.own 1) vs ∗ ⌜l ≠ null⌝) $$ [Hl]
  · inext
    icases (typed.typedPointsto_encoded l v' _).1 $$ Hl with ⟨%vs'', %Hvs'', %Hnn, H⟩
    rw [hvs] at Hvs''; cases Hvs''
    iframe H; ipureintro; exact Hnn
  icases Hl with ⟨Hl, >%Hnn⟩
  iapply wp_cmpxchgN_suc enc l vs vs2 #v' #v1 #v2 hal (encode_length hvs) (decode_encode hvs)
    (congrArg _ heq) hvs2 $$ Hl
  inext; iintro Hl
  iapply HΦ
  iapply (typed.typedPointsto_encoded l v2 _).2
  iexists vs2; iframe Hl; ipureintro; exact ⟨hvs2, Hnn⟩

/-- The atomic add of a word. -/
theorem typed.wp_atomic_add {n : Nat} [hW : EncodedPointsto (GF := GF) V (.word n)] (l : Loc) (v d r : V)
    (hal : Aligned (.word n) l) (hadd : atomicAddEval #v #d = some #r) :
    {{ ▷ (l ↦ v : IProp GF) }} (AddN (.word n) (Val #l) (Val #d)) @ s; E {{ RET #r; l ↦ r }} := by
  iintro %Φ Hl HΦ
  obtain ⟨vs, hvs⟩ := hW.encode_some v
  obtain ⟨vs', hvs'⟩ := hW.encode_some r
  ihave Hl : ▷ (pointstoVals l (DFrac.own 1) vs ∗ ⌜l ≠ null⌝) $$ [Hl]
  · inext
    icases (typed.typedPointsto_encoded (hE := hW) l v _).1 $$ Hl with ⟨%vs'', %Hvs'', %Hnn, H⟩
    rw [hvs] at Hvs''; cases Hvs''
    iframe H; ipureintro; exact Hnn
  icases Hl with ⟨Hl, >%Hnn⟩
  iapply wp_addN n l vs vs' #v #d #r hal (by rw [encode_length hvs]; rfl) (decode_encode hvs)
    hadd hvs' $$ Hl
  inext; iintro Hl
  iapply HΦ
  iapply (typed.typedPointsto_encoded (hE := hW) l r _).2
  iexists vs'; iframe Hl; ipureintro; exact ⟨hvs', Hnn⟩

include hE in
/-- A full points-to and a discarded one of an encoded value are not at the same place. -/
theorem word_pointsto_own_discard (l : Loc) (v w : V) :
    (l ↦ v ∗ l ↦□ w : IProp GF) ⊢ False := by
  iintro ⟨H1, H2⟩
  icases (typed.typedPointsto_encoded (GF := GF) l v (DFrac.own 1)).1 $$ H1 with ⟨%vs1, %h1, -, H1⟩
  icases (typed.typedPointsto_encoded (GF := GF) l w DFrac.discard).1 $$ H2 with ⟨%vs2, %h2, -, H2⟩
  obtain ⟨c1, cs1, rfl⟩ := List.exists_cons_of_ne_nil (encode_some_ne_nil h1)
  obtain ⟨c2, cs2, rfl⟩ := List.exists_cons_of_ne_nil (encode_some_ne_nil h2)
  unfold pointstoVals
  icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨H1, -⟩
  icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨H2, -⟩
  icombine H1 H2 gives %H
  exact absurd (DFrac.valid_own_op_discard.1 H.1) (by simp)

include hE in
/-- Two full points-tos of an encoded value are not at the same place. -/
theorem word_pointsto_excl (l : Loc) (v w : V) :
    (l ↦ v ∗ l ↦ w : IProp GF) ⊢ False := by
  iintro ⟨H1, H2⟩
  icases (typed.typedPointsto_encoded (GF := GF) l v (DFrac.own 1)).1 $$ H1 with ⟨%vs1, %h1, -, H1⟩
  icases (typed.typedPointsto_encoded (GF := GF) l w (DFrac.own 1)).1 $$ H2 with ⟨%vs2, %h2, -, H2⟩
  obtain ⟨c1, cs1, rfl⟩ := List.exists_cons_of_ne_nil (encode_some_ne_nil h1)
  obtain ⟨c2, cs2, rfl⟩ := List.exists_cons_of_ne_nil (encode_some_ne_nil h2)
  unfold pointstoVals
  icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨H1, -⟩
  icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨H2, -⟩
  icombine H1 H2 gives %H
  exact absurd (DFrac.valid_op_own H.1) (by simp)

end atomic_wps

instance encoded_w64 : EncodedPointsto (GF := GF) w64 (.word 8) :=
  ⟨fun _ _ _ => .rfl, encode_w64 (hG := hG), go.intoVal_inj⟩
instance encoded_w32 : EncodedPointsto (GF := GF) w32 (.word 4) :=
  ⟨fun _ _ _ => .rfl, encode_w32 (hG := hG), go.intoVal_inj⟩
instance encoded_w16 : EncodedPointsto (GF := GF) w16 (.word 2) :=
  ⟨fun _ _ _ => .rfl, encode_w16 (hG := hG), go.intoVal_inj⟩
instance encoded_w8 : EncodedPointsto (GF := GF) w8 (.word 1) :=
  ⟨fun _ _ _ => .rfl, encode_w8 (hG := hG), go.intoVal_inj⟩
instance encoded_loc : EncodedPointsto (GF := GF) Loc (.cell 8) :=
  ⟨fun _ _ _ => .rfl, fun v => encode_cell 8 (by decide) #v, go.intoVal_inj⟩
instance encoded_bool : EncodedPointsto (GF := GF) Bool (.cell 1) :=
  ⟨typedPointstoDef_bool, fun v => encode_cell 1 (by decide) #v, go.intoVal_inj⟩
instance encoded_interface : EncodedPointsto (GF := GF) GoInterface (.cell 16) :=
  ⟨fun _ _ _ => .rfl, fun v => encode_cell 16 (by decide) #v, go.intoVal_inj⟩

end goose_lang

/-! ## Access to (sub-)points-to facts -/

/-- `AccessStrict A A' P P'`: from `P` one can take out `A`, and putting back
`A'` gives `P'` (e.g. a struct field points-to from a struct points-to). -/
@[ipm_class]
class AccessStrict {PROP : Type _} [BI PROP] (A A' : PROP) (P P' : outParam PROP) : Prop where
  access_strict : P ⊢ A ∗ (A' -∗ P')

/-- The reflexive-transitive closure of `AccessStrict`. -/
@[ipm_class]
class Access {PROP : Type _} [BI PROP] (A A' P : PROP) (P' : outParam PROP) : Prop where
  access : P ⊢ A ∗ (A' -∗ P')

export AccessStrict (access_strict)
export Access (access)

@[ipm_backtrack]
instance access_transitive {PROP : Type _} [BI PROP] {Q P P' Q' A A' : PROP}
    [h1 : AccessStrict A A' P P'] [h2 : Access P P' Q Q'] : Access A A' Q Q' where
  access := by
    iintro H
    icases h2.access $$ H with ⟨H, Hwand⟩
    icases h1.access_strict $$ H with ⟨H, Hwand'⟩
    iframe H
    iintro H
    iapply Hwand
    iapply Hwand' $$ H

instance access_trivial {PROP : Type _} [BI PROP] (P P' : PROP) : Access P P' P P' where
  access := by iintro H; iframe H; iintro H; iexact H

/-! ## Tactic lemmas -/

section alloc_aligned
open Iris.ProofMode
variable [FfiSyntax] [GoSemanticsFunctions] {PROP : Type _} [BI PROP]

/-- The alignment of a fresh allocation (`AllocAligned`), as the persistent hypothesis
`x_al` that the allocation tactics add. It is opaque so that framing leaves it alone;
`icases x_al with %h` gives the fact. -/
@[irreducible] def allocAligned (V : Type) (l : Loc) : PROP := iprop(⌜AllocAligned V l⌝)

theorem allocAligned_intro {V : Type} {l : Loc} (h : AllocAligned V l) :
    ⊢ (allocAligned V l : PROP) := by
  unfold allocAligned; exact BI.pure_intro h

instance allocAligned_persistent (V : Type) (l : Loc) :
    Persistent (allocAligned V l : PROP) := by
  unfold allocAligned; infer_instance

instance allocAligned_intoPure (V : Type) (l : Loc) :
    IntoPure (allocAligned V l : PROP) (AllocAligned V l) := by
  unfold allocAligned; infer_instance

end alloc_aligned

section tac_lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

theorem access_split {Δ Δ' P A : IProp GF} {p : Bool} [h : Access A A P P]
    (hsplit : Δ ⊣⊢ Δ' ∗ iprop(□?p P)) : Δ ⊢ A ∗ (A -∗ Δ) := by
  cases p
  · have hsplit : Δ ⊣⊢ Δ' ∗ P := hsplit
    iintro HΔ
    icases hsplit.1 $$ HΔ with ⟨HΔ', HP⟩
    icases h.access $$ HP with ⟨HA, Hclose⟩
    iframe HA
    iintro HA
    iapply hsplit.2
    iframe HΔ'
    iapply Hclose $$ HA
  · have hsplit : Δ ⊣⊢ Δ' ∗ iprop(□ P) := hsplit
    iintro HΔ
    icases hsplit.1 $$ HΔ with ⟨HΔ', #HP⟩
    icases h.access $$ HP with ⟨HA, -⟩
    iframe HA
    iintro -
    iapply hsplit.2
    iframe HΔ' HP

theorem tac_wp_load {V : Type} {t : go.GoType} [ZeroVal V] [tpt : TypedPointsto (GF := GF) V]
    [IntoValTyped (GF := GF) V t] {K : List EctxItem} {l : Loc} {v : V} {dq : DFrac}
    {Δ Δ' P : IProp GF} {p : Bool} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    [hacc : Access (l ↦{dq} v) (l ↦{dq} v) P P]
    (hsplit : Δ ⊣⊢ Δ' ∗ iprop(□?p P)) (h : Δ ⊢ WP (fill K (Val #v)) @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K (App (Val (GoInstruction (GoLoad t))) (Val #l))) @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_bind (fill K))
  refine (access_split (h := hacc) hsplit).trans ?_
  iintro ⟨HA, Hclose⟩
  iapply IntoValTyped.wp_load (t := t) l dq v $$ HA
  inext
  iintro HA
  iapply h
  iapply Hclose $$ HA

theorem tac_wp_store {V : Type} {t : go.GoType} [ZeroVal V] [tpt : TypedPointsto (GF := GF) V]
    [IntoValTyped (GF := GF) V t] {K : List EctxItem} {l : Loc} {v w : V}
    {Δ Δ' Δ'' P P' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    [hacc : Access (l ↦ v) (l ↦ w) P P']
    (hsplit : Δ ⊣⊢ Δ' ∗ P) (hadd : Δ' ∗ P' ⊣⊢ Δ'')
    (h : Δ'' ⊢ WP (fill K (Val #())) @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w)))) @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_bind (fill K))
  refine hsplit.1.trans ?_
  iintro ⟨HΔ', HP⟩
  icases hacc.access $$ HP with ⟨HA, Hclose⟩
  iapply IntoValTyped.wp_store (t := t) l v w $$ HA
  inext
  iintro HA
  iapply h
  iapply hadd.1
  iframe HΔ'
  iapply Hclose $$ HA

theorem tac_add_hyp2 {PROP : Type _} [BI PROP] {Δ Δ0 Δ' A P Q : PROP}
    (hadd0 : iprop(Δ ∗ □?true A) ⊣⊢ Δ0) (hadd : iprop(Δ0 ∗ □?false P) ⊣⊢ Δ') (h : Δ' ⊢ Q) :
    iprop((Δ ∗ □ A) ∗ P) ⊢ Q :=
  (BI.sep_mono_left hadd0.1).trans (hadd.1.trans h)

theorem tac_wp_alloc {V : Type} {t : go.GoType} [ZeroVal V] [tpt : TypedPointsto (GF := GF) V]
    [IntoValTyped (GF := GF) V t] {K : List EctxItem} {v : V}
    {Δ : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (h : ∀ l : Loc, iprop((Δ ∗ □ allocAligned V l) ∗ (l ↦ v)) ⊢
      WP (fill K (Val #l)) @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K (App (Val (GoInstruction (GoAlloc t))) (Val #v))) @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_bind (fill K))
  iintro HΔ
  iapply IntoValTyped.wp_alloc (t := t) v
  · itrivial
  inext
  iintro %l ⟨Hl, %Hal⟩
  iapply h l
  iframe
  imodintro
  iapply allocAligned_intro Hal

end tac_lemmas

section func_lit
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [go.PreSemantics]

/-- A function literal value is the Go function value `#(func.mk f x e)` (used
by `wp_store` to store function literals). -/
theorem recv_eq_func_mk (f x : Binder) (e : Expr) : (RecV f x e : val) = #(func.mk f x e) := by
  rw [go.intoVal_unfold GoFunc]

end func_lit

/-! ## The memory tactics -/

section tactics
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- If `e` is `#x` (`intoVal x`), return `(V, x)`. -/
meta def isIntoVal? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let e ← instantiateMVars e
  let e := e.consumeMData
  if e.isAppOfArity ``GoGlobalContext.intoVal 4 then
    return some (e.getArg! 2, e.getArg! 3)
  return none

/-- If `e` is `Val (GoInstruction i)` applied to `arg` with `i` satisfying
`instr`, return `(i, arg)`. -/
meta def isGoInstrApp? (e : Lean.Expr) (instr : Name) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let e ← whnfR (← instantiateMVars e)
  let_expr Perennial.Expr.App _ f arg := e | return none
  let some fv ← isGooseVal? f | return none
  let fv ← whnfR fv
  let_expr Perennial.val.GoInstruction _ i := fv | return none
  let i ← whnfR i
  unless i.isAppOf instr do return none
  let some argv ← isGooseVal? arg | return none
  return some (i, argv)

-- `hypsList` (all hypotheses of an Iris context) is in `PostLifting.lean`.

/-- The hypotheses of `hyps` (as `hypsList`), with those that are a typed
points-to at exactly the address `l` first: these are tried first by
`wp_load`/`wp_store`, so that the common case needs a single `Access` search
instead of one per hypothesis. -/
meta def hypsListFor {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e) (l : Lean.Expr) :
    MetaM (List (Name × IVarId × Q(Bool) × Q($prop))) := do
  let mut exact := #[]
  let mut rest := #[]
  for h@(_, _, _, ty) in hypsList hyps do
    let ty ← instantiateMVars ty
    if ty.isAppOfArity ``typedPointsto 6 && ty.getArg! 3 == l then exact := exact.push h
    else rest := rest.push h
  return exact.toList ++ rest.toList

/-- The typed points-to `@typedPointsto GF V inst l v dq`, with fresh
metavariables for `V`, the `TypedPointsto` instance, `v` (unless given) and
`dq` (unless given). -/
meta def mkTypedPointstoMVars (GF l : Lean.Expr) (V? v? dq? : Option Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let V ← match V? with | some V => pure V | none => mkFreshExprMVar (mkSort (mkLevelSucc .zero))
  let instTy ← mkAppOptM ``TypedPointsto #[some GF, some V]
  let inst ← mkFreshExprMVar instTy
  let v ← match v? with | some v => pure v | none => mkFreshExprMVar V
  let dq ← match dq? with | some dq => pure dq | none => mkFreshExprMVar (mkConst ``DFrac)
  let pt ← mkAppOptM ``typedPointsto #[some GF, some V, some inst, some l, some v, some dq]
  return (pt, V, inst, v, dq)

/-- Search for `Access A A' P ?P'` with the proof mode's typeclass search. -/
meta def synthAccess (A A' P : Lean.Expr) : ProofModeM (Option (Lean.Expr × Lean.Expr)) := do
  let P' ← mkFreshExprMVar (← inferType P)
  let ty ← mkAppM ``Access #[A, A', P, P']
  match ← ProofMode.trySynthInstance ty with
  | .some (inst, _) => return some (inst, ← instantiateMVars P')
  | _ => return none

/-- One `wp_load` step: find `![t] #l` in evaluation position and a hypothesis
`P` (spatial or intuitionistic) with `Access (l ↦{dq} v) (l ↦{dq} v) P P`;
the load returns `#v` and keeps the context. Also returns the loaded value `#v`. -/
meta def iWpLoadStepV {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Lean.Expr × (Lean.Expr → MetaM Lean.Expr) × Lean.Expr) := do
  let some ((t, l), K, _) ← findEctx wp.e (fun _ e => do
      let some (i, lv) ← isGoInstrApp? e ``GoInstruction.GoLoad | throwError "no"
      let some (_, l) ← isIntoVal? lv | throwError "no"
      return (i.getArg! 1, l))
    | throwIPMError "could not find a load `![t] #l`"
  let GF := (← gooseGSArgs wp.ι)[6]!
  for (_, ivar, p, P) in ← hypsListFor hyps l do
    let saved ← saveState
    -- the fraction of a typed points-to hypothesis is the one to load at (a struct's
    -- field points-tos have its fraction): with a fresh one, a store instance (at
    -- `DFrac.own 1`) would also match a load through a fractional struct points-to
    let P ← instantiateMVars P
    let dq? := if P.isAppOfArity ``typedPointsto 6 then some (P.getArg! 5) else none
    let (A, V, inst, v, dq) ← mkTypedPointstoMVars GF l none none dq?
    if let some (hacc, P') ← synthAccess A A P then
      if ← isDefEq P' P then
        let r := hyps.remove true ivar
        let v ← instantiateMVars v
        let vv ← instantiateMVars (← mkAppOptM ``GoGlobalContext.intoVal
          #[none, none, some (← instantiateMVars V), some v])
        let filled ← fillExpr K (mkApp2 (mkConst ``Perennial.Expr.Val) wp.ext vv)
        let k := fun (h : Lean.Expr) => do
          let V ← instantiateMVars V
          let inst ← instantiateMVars inst
          wp.mkAppNamed ``tac_wp_load
            [("Δ", ehyps), ("Δ'", r.e'), ("Φ", wp.Φ),
             ("V", V), ("t", t), ("K", wp.quoteK K), ("l", l), ("v", v),
             ("dq", ← instantiateMVars dq), ("p", r.p), ("P", P),
             ("s", wp.s), ("E", wp.E), ("tpt", inst), ("hacc", hacc),
             ("hsplit", r.pf), ("!h", h)]
        let _ := p
        return ⟨ehyps, hyps, filled, k, vv⟩
    restoreState saved
  throwIPMError "could not find a points-to in context covering the address {l}"

/-- `iWpLoadStepV` without the loaded value. -/
meta def iWpLoadStep {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Lean.Expr × (Lean.Expr → MetaM Lean.Expr)) := do
  let ⟨_, hyps', e', k, _⟩ ← iWpLoadStepV hyps wp
  return ⟨_, hyps', e', k⟩

/-- One `wp_store` step: find `GoStore t (#l, #w)` and a spatial hypothesis
`P` with `Access (l ↦ v) (l ↦ w) P P'`; `P` is replaced by `P'` (same name). -/
meta def iWpStoreStep {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Lean.Expr × (Lean.Expr → MetaM Lean.Expr)) := do
  let some ((t, l, W, w), K, _) ← findEctx wp.e (fun _ e => do
      let some (i, arg) ← isGoInstrApp? e ``GoInstruction.GoStore | throwError "no"
      let arg ← whnfR arg
      let_expr Perennial.val.PairV _ lv wv := arg | throwError "no"
      let some (_, l) ← isIntoVal? lv | throwError "no"
      let some (W, w) ← isIntoVal? wv | throwError "no"
      return (i.getArg! 1, l, W, w))
    | throwIPMError "could not find a store `GoStore t (#l, #w)`"
  let GF := (← gooseGSArgs wp.ι)[6]!
  -- (instantiated: an assigned instance metavariable in the context would make every
  -- later `instantiateMVars` of the context traverse it)
  let own1 ← instantiateMVars (← mkAppM ``DFrac.own
    #[← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Iris.Qp), some (mkRawNatLit 1), none]])
  for (name, ivar, p, P) in ← hypsListFor hyps l do
    if isTrue p then continue
    let saved ← saveState
    let (A, _, inst, v, _) ← mkTypedPointstoMVars GF l (some W) none (some own1)
    let A' ← mkAppOptM ``typedPointsto #[some GF, some W, some inst, some l, some w, some own1]
    if let some (hacc, P') ← synthAccess A A' P then
      let r := hyps.remove true ivar
      let ⟨ehyps'', hyps'', hadd⟩ := r.hyps'.add bi name ivar q(false) P'
      let unitV ← instantiateMVars (← mkAppOptM ``GoGlobalContext.intoVal
        #[none, none, some (mkConst ``Unit), some (mkConst ``Unit.unit)])
      let filled ← fillExpr K (mkApp2 (mkConst ``Perennial.Expr.Val) wp.ext unitV)
      let k := fun (h : Lean.Expr) => do
        wp.mkAppNamed ``tac_wp_store
          [("Δ", ehyps), ("Δ'", r.e'), ("Δ''", ehyps''), ("Φ", wp.Φ),
           ("V", W), ("t", t), ("K", wp.quoteK K), ("l", l), ("v", ← instantiateMVars v),
           ("w", w), ("P", P), ("P'", P'),
           ("s", wp.s), ("E", wp.E), ("tpt", ← instantiateMVars inst),
           ("hacc", hacc), ("hsplit", r.pf), ("hadd", hadd), ("!h", h)]
      return ⟨_, hyps'', filled, k⟩
    restoreState saved
  throwIPMError "could not find a points-to in context covering the address {l}"

/-- If the WP expression stores a function literal, `GoStore t (#l, RecV f x e)`,
rewrite the stored value to the Go function value `#(func.mk f x e)`
(`recv_eq_func_mk`), so that `wp_store` can use the typed points-to at `GoFunc`.
Returns the new (inner) expression and a function turning a proof of the new goal
into a proof of the old one. -/
meta def iWpStoreFuncLit? (wp : GooseWpGoal) (Δ : Lean.Expr) :
    ProofModeM (Option (Lean.Expr × (Lean.Expr → MetaM Lean.Expr))) := do
  let some ((sv, lv, f, x, body), K, _) ← findEctx (α := Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) wp.e
      (fun _ e => do
        let e ← whnfR e
        let_expr Perennial.Expr.App _ fe arg := e | throwError "no"
        let some _ ← isGoInstrApp? e ``GoInstruction.GoStore | throwError "no"
        let some argv ← isGooseVal? arg | throwError "no"
        let argv ← whnfR argv
        let_expr Perennial.val.PairV _ lv wv := argv | throwError "no"
        if (← isIntoVal? wv).isSome then throwError "no"
        let wv ← whnfR wv
        let_expr Perennial.val.RecV _ f x body := wv | throwError "no"
        return (fe, lv, f, x, body))
    | return none
  let _ := sv
  let ext := wp.ext
  let pf ← mkAppM ``recv_eq_func_mk #[f, x, body]
  let valTy := mkApp (mkConst ``Perennial.val) ext
  let motive ← withLocalDeclD `w valTy fun w => do
    let pair := mkApp3 (mkConst ``Perennial.val.PairV) ext lv w
    let inner := mkApp3 (mkConst ``Perennial.Expr.App) ext sv (mkApp2 (mkConst ``Perennial.Expr.Val) ext pair)
    mkLambdaFVars #[w] (wp.wrap (← fillExpr K inner))
  let heq ← mkCongrArg motive pf
  let some (_, _, rhs) := (← instantiateMVars (← inferType heq)).eq? | return none
  let rhs ← instantiateMVars rhs
  let e' := match wp.tail with
    | none => rhs.headBeta
    | some _ => rhs.headBeta.appArg!
  let lhs := (mkApp motive (mkApp4 (mkConst ``Perennial.val.RecV) ext f x body)).headBeta
  return some (e', fun h => wp.mkAppNamed ``tac_wp_expr_simp
    [("Δ", Δ), ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ), ("e", lhs), ("e'", wp.wrap e'),
     ("!h", h), ("!heq", heq)])

/-- A `wp_alloc` step: find `GoAlloc t #v` (optionally only as the argument of
`let: "x" := _ in _`, when `auto`), and continue under a fresh location `l`
with the new hypothesis `l ↦ v` and the intuitionistic `x_al : allocAligned V l` (the
allocation's alignment, for atomic operations). `names` gives the Lean and Iris names
(from the `let:` binder when `auto`: `x_ptr` and `x`). -/
meta def iWpAllocStep {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (auto : Bool)
    (names : Option (Name × Name))
    (k : ∀ {ehyps' : Q($prop)}, Hyps bi ehyps' → GooseWpGoal → ProofModeM Lean.Expr) :
    ProofModeM Lean.Expr := do
  let some ((t, V, v, letName?), K, _) ← findEctx wp.e (fun K e => do
      let some (i, vv) ← isGoInstrApp? e ``GoInstruction.GoAlloc | throwError "no"
      let some (V, v) ← isIntoVal? vv | throwError "no"
      -- the `let:` binder name, from the enclosing evaluation context item
      let letName? ← match K with
        | Ki :: _ =>
          let Ki ← whnfR Ki
          if Ki.isAppOfArity ``EctxItem.AppRCtx 2 then
            let f ← whnfR (Ki.getArg! 1)
            match_expr f with
            | Perennial.Expr.Rec _ fb xb _ =>
              let fb ← whnfR fb; let xb ← whnfR xb
              if fb.isAppOf ``Binder.BAnon then
                match_expr xb with
                | Binder.BNamed s =>
                  match (← whnfR s) with
                  | .lit (.strVal s) => pure (some s)
                  | _ => pure none
                | _ => pure none
              else pure none
            | _ => pure none
          else pure none
        | [] => pure none
      if auto && letName?.isNone then throwError "no"
      return (i.getArg! 1, V, v, letName?))
    | throwIPMError "could not find an allocation `GoAlloc t #v`"
  let (lName, hName) := match names, letName? with
    | some ns, _ => ns
    | none, some x => (Name.mkSimple (x ++ "_ptr"), Name.mkSimple x)
    | none, none => (`l, `Hl)
  let GF := (← gooseGSArgs wp.ι)[6]!
  -- (instantiated: an assigned instance metavariable in the context would make every
  -- later `instantiateMVars` of the context traverse it)
  let own1 ← instantiateMVars (← mkAppM ``DFrac.own
    #[← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Iris.Qp), some (mkRawNatLit 1), none]])
  let instTy ← mkAppOptM ``TypedPointsto #[some GF, some V]
  let inst ← synthInstance instTy
  let locTy := mkConst ``Perennial.Loc
  -- the continuation `∀ l, Δ ∗ l ↦ v ⊢ WP K[#l]` is a metavariable, introduced with
  -- `MVarId.intro` (a delayed assignment), so that the (large) continuation proof is
  -- not abstracted over `l` here (that made `wp_auto` quadratic)
  let mkParts (l : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
    let pt ← instantiateMVars
      (← mkAppOptM ``typedPointsto #[some GF, some V, some inst, some l, some v, some own1])
    let lv ← instantiateMVars
      (← mkAppOptM ``GoGlobalContext.intoVal #[none, none, some locTy, some l])
    let filled ← fillExpr K (mkApp2 (mkConst ``Perennial.Expr.Val) wp.ext lv)
    return (pt, filled)
  let mkAl (l : Lean.Expr) : MetaM Lean.Expr := do
    instantiateMVars (← mkAppOptM ``allocAligned #[none, none, some prop, none, some V, some l])
  let alName := hName.appendAfter "_al"
  let hTy ← withLocalDeclD lName locTy fun l => do
    let (pt, filled) ← mkParts l
    let al ← mkAl l
    let alI ← instantiateMVars (← mkAppOptM ``BIBase.intuitionistically #[some prop, none, some al])
    let ehyps0 ← instantiateMVars (← mkAppOptM ``BIBase.sep #[some prop, none, some ehyps, some alI])
    let lhs ← instantiateMVars (← mkAppOptM ``BIBase.sep #[some prop, none, some ehyps0, some pt])
    let T ← instantiateMVars
      (← mkAppOptM ``BIBase.Entails #[some prop, none, some lhs, some (wp.mk' filled wp.Φ)])
    mkForallFVars #[l] T
  let m ← mkFreshExprSyntheticOpaqueMVar hTy
  binderSteps.modify (· + 1)
  let (l, m') ← m.mvarId!.intro lName
  m'.withContext do
    let l := mkFVar l
    let (pt, filled) ← mkParts l
    let al : Q($prop) ← mkAl l
    let ivar0 ← mkFreshIVarId true
    let ⟨ehyps0, hyps0, hadd0⟩ := hyps.add bi alName ivar0 q(true) al
    let ivar ← mkFreshIVarId false
    let ⟨ehyps', hyps', hadd⟩ := hyps0.add bi hName ivar q(false) pt
    let pfCont ← k hyps' { wp with e := filled }
    -- `hadd : Δ0 ∗ □?false (l ↦ v) ⊣⊢ Δ'`, `hadd0 : Δ ∗ □?true ⌜…⌝ ⊣⊢ Δ0`
    let pfl ← mkAppNamed ``tac_add_hyp2
      [("PROP", prop), ("Δ", ehyps), ("Δ0", ehyps0), ("Δ'", ehyps'), ("Q", wp.mk' filled wp.Φ),
       ("A", al), ("P", pt), ("hadd0", hadd0), ("hadd", hadd), ("!h", pfCont)]
    m'.assign pfl
  let pf := m
  wp.mkAppNamed ``tac_wp_alloc
    [("Δ", ehyps), ("Φ", wp.Φ), ("V", V), ("t", t), ("K", wp.quoteK K), ("v", v),
     ("s", wp.s), ("E", wp.E), ("tpt", inst), ("!h", pf)]

end tactics

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_load` performs a typed load `![t] #l` in evaluation position, using a
hypothesis covering `l`: either `l ↦{dq} v` itself, or a hypothesis from which
it can be accessed (`Access` instance, e.g. a struct points-to for a field
address). The load produces `#v`. -/
elab "wp_load" : tactic =>
  runTacticGooseWp `wp_load fun mvar g wp => do
    let ⟨_, hyps', e', k⟩ ← iWpLoadStep g.hyps wp
    mvar.assign (← k (← iWpFinish hyps' { wp with e := e' }))

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_store` performs a typed store `GoStore t (#l, #w)` in evaluation
position, using a spatial hypothesis covering `l` with full ownership, which is
updated to the new value. -/
elab "wp_store" : tactic =>
  runTacticGooseWp `wp_store fun mvar g wp => do
    -- a stored function literal `RecV f x e` is first rewritten to `#(func.mk f x e)`
    let (wp, k0) ← match ← iWpStoreFuncLit? wp g.e with
      | some (e', k0) => pure ({ wp with e := e' }, k0)
      | none => pure (wp, pure)
    let ⟨_, hyps', e', k⟩ ← iWpStoreStep g.hyps wp
    mvar.assign (← k0 (← k (← iWpFinish hyps' { wp with e := e' })))

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_alloc l as H` performs an allocation `GoAlloc t #v` in evaluation
position, introducing the location `l` and the hypothesis `H : l ↦ v`. -/
elab "wp_alloc " l:ident " as " H:ident : tactic =>
  runTacticGooseWp `wp_alloc fun mvar g wp => do
    mvar.assign (← iWpAllocStep g.hyps wp false (some (l.getId, H.getId))
      fun hyps' wp' => iWpFinish hyps' wp')

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_alloc_auto` performs an allocation `let: "x" := GoAlloc t #v in e`,
naming the location `x_ptr` and the points-to `x`. If there is no `let:`-bound
allocation, an anonymous allocation (e.g. `&S{..}`) is performed, with
inaccessible names. (`wp_auto` only does `let:`-bound allocations.) -/
elab "wp_alloc_auto" : tactic =>
  runTacticGooseWp `wp_alloc_auto fun mvar g wp => do
    let saved ← saveState
    try
      mvar.assign (← iWpAllocStep g.hyps wp true none fun hyps' wp' => iWpFinish hyps' wp')
    catch _ =>
      saved.restore
      let l ← mkFreshUserName `l
      let H ← mkFreshUserName `H
      mvar.assign (← iWpAllocStep g.hyps wp false (some (l, H)) fun hyps' wp' => iWpFinish hyps' wp')

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_alloc_anon`: perform an allocation
`GoAlloc t #v` in evaluation position (not necessarily bound by `let:`), with
inaccessible names. -/
elab "wp_alloc_anon" : tactic =>
  runTacticGooseWp `wp_alloc_anon fun mvar g wp => do
    let l ← mkFreshUserName `l
    let H ← mkFreshUserName `H
    mvar.assign (← iWpAllocStep g.hyps wp false (some (l, H)) fun hyps' wp' => iWpFinish hyps' wp')

section access_struct
variable [FfiSyntax] {GF : BundledGFunctors} {V : Type} [TypedPointsto (GF := GF) V]
open ProofMode

/-- Focusing on a conjunct of a right-nested `∗`-chain: here. -/
theorem sep_focus_here {X T : IProp GF} : iprop(X ∗ T) ⊣⊢ iprop(X ∗ T) := .rfl
/-- Focusing on a conjunct of a right-nested `∗`-chain: further right. -/
theorem sep_focus_there {F T X R : IProp GF} (h : T ⊣⊢ iprop(X ∗ R)) :
    iprop(F ∗ T) ⊣⊢ iprop(X ∗ (F ∗ R)) :=
  (sep_congr_right h).trans sep_left_comm
/-- Focusing on the last conjunct of a `∗`-chain. -/
theorem sep_focus_last {F X : IProp GF} : iprop(F ∗ X) ⊣⊢ iprop(X ∗ F) := sep_comm

/-- An `AccessStrict` instance for a struct field from the focusing of the field
in the struct's points-to before and after the update (with the same rest `R`). -/
theorem access_struct_field {l : Loc} {v v' : V} {dq : DFrac} {A A' R : IProp GF}
    (hP : typedPointstoDef l v dq ⊣⊢ iprop(A ∗ R))
    (hP' : typedPointstoDef l v' dq ⊣⊢ iprop(A' ∗ R)) :
    AccessStrict A A' (typedPointsto l v dq) (typedPointsto l v' dq) where
  access_strict := by
    rw [typedPointsto_unseal]; unfold typedPointstoWrap
    iintro ⟨H, %Hnn⟩
    icases hP.1 $$ H with ⟨HA, HR⟩
    iframe HA
    iintro HA'
    isplitl [HA' HR]
    · iapply hP'.2; iframe
    · ipureintro; exact Hnn

end access_struct

section access_struct_tac
open Lean Elab Tactic Meta

/-- The conjuncts of a right-nested `∗`-chain (`named` wrappers are kept). -/
meta partial def sepChain (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let e ← whnfR e
  if e.isAppOfArity ``Iris.BI.BIBase.sep 4 then
    return #[e.getArg! 2] ++ (← sepChain (e.getArg! 3))
  return #[e]

/-- A proof of `chain ⊣⊢ X ∗ R` (and `R`) focusing on the conjunct number `k` of
the chain `P` (`P` itself as an expression). -/
meta partial def focusPf (P : Lean.Expr) (k : Nat) : MetaM (Lean.Expr × Lean.Expr) := do
  let P' ← whnfR P
  unless P'.isAppOfArity ``Iris.BI.BIBase.sep 4 do throwError "focusPf: not a ∗"
  let F := P'.getArg! 2; let T := P'.getArg! 3
  if k == 0 then
    return (← mkAppOptM ``sep_focus_here #[none, none, F, T], T)
  -- the last conjunct of the chain
  if k == 1 && !(← whnfR T).isAppOfArity ``Iris.BI.BIBase.sep 4 then
    return (← mkAppOptM ``sep_focus_last #[none, none, F, T], F)
  let (h, R) ← focusPf T (k - 1)
  let ty ← instantiateMVars (← inferType h)
  unless ty.isAppOf ``Iris.BI.BIBase.BiEntails do throwError "focusPf: {ty}"
  let rhs ← whnfR ty.getAppArgs.back!
  let X := rhs.getArg! 2
  let FR ← mkAppOptM ``Iris.BI.BIBase.sep #[none, none, F, R]
  return (← mkAppOptM ``sep_focus_there #[none, none, F, T, X, R, h], FR)

/-- Prove an `AccessStrict` instance for a
struct field (`AccessStrict A A' (l ↦{dq} v) (l ↦{dq} v')`, with `v'` the struct
with the field updated). Linear in the number of fields: the field is focused in
the unfolded struct points-to by `sep_focus_*` lemmas (no framing). -/
elab "solve_pointsto_access_struct" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let ty ← whnfR ty
  unless ty.isAppOf ``AccessStrict do throwError "solve_pointsto_access_struct: not an AccessStrict goal"
  let args := ty.getAppArgs
  let A := args[args.size - 4]!; let A' := args[args.size - 3]!
  let P := args[args.size - 2]!; let P' := args[args.size - 1]!
  -- `P = typedPointsto l v dq`
  let P ← instantiateMVars P; let P' ← instantiateMVars P'
  let defOf (Q : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
    unless Q.isAppOf ``typedPointsto do throwError "solve_pointsto_access_struct: {Q} is not a typed points-to"
    let a := Q.getAppArgs
    -- `typedPointstoDef l v dq` (same implicit arguments)
    let d ← mkAppOptM ``TypedPointsto.typedPointstoDef
      #[none, a[a.size - 5]!, a[a.size - 4]!, a[a.size - 3]!, a[a.size - 2]!, a[a.size - 1]!]
    -- unfold the instance to the chain of fields
    let some d' ← unfoldProjInst? d | throwError "solve_pointsto_access_struct: cannot unfold {d}"
    return ((d, d'.headBeta) : Lean.Expr × Lean.Expr)
  let (d, chain) ← defOf P
  let (d', chain') ← defOf P'
  let cs ← sepChain chain
  -- the field: the conjunct (up to `named`) that is `A`
  let unNamed (e : Lean.Expr) : Lean.Expr := if e.isAppOfArity ``named 3 then e.getArg! 2 else e
  let mut k? := none
  for h : i in [:cs.size] do
    if ← withReducible (isDefEq (unNamed cs[i]) A) then k? := some i; break
  let some k := k? | throwError "solve_pointsto_access_struct: field {A} not found in{indentExpr chain}"
  let (h1, R) ← focusPf chain k
  let (h2, _) ← focusPf chain' k
  -- `d ⊣⊢ A ∗ R` and `d' ⊣⊢ A' ∗ R` (definitionally)
  let ty1 ← mkAppM ``Iris.BI.BIBase.BiEntails #[d, ← mkAppM ``Iris.BI.BIBase.sep #[A, R]]
  let ty2 ← mkAppM ``Iris.BI.BIBase.BiEntails #[d', ← mkAppM ``Iris.BI.BIBase.sep #[A', R]]
  let pf ← mkAppM ``access_struct_field #[← mkExpectedTypeHint h1 ty1, ← mkExpectedTypeHint h2 ty2]
  let pf ← mkExpectedTypeHint pf (← g.getType)
  g.assign pf
  replaceMainGoal []

end access_struct_tac

end Perennial
