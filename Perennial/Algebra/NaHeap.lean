/-
Non-atomic heap.

A heap that supports non-atomic operations: each location carries a lock state
(`WSt` while being written, `RSt n` while `n` readers are active). Adapted from
lambda-rust by Jung et al.

The ghost state is only the value heap: `naHeapCtx` is the authoritative heap
view over a `Perennial.gmap`, with no per-location metadata or block sizes.
-/
module

public import Iris.Algebra.HeapView
public import Iris.Algebra.Csum
public import Iris.Algebra.Agree
public import Iris.Algebra.Numbers
public import Iris.Instances.IProp
public import Iris.Instances.Lib.LaterCredits
public import Iris.BI.Lib.Fractional
public import Iris.ProofMode
public import Perennial.Std.GMap
public import Perennial.IrisLib.DFractional

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.Algebra Iris.Std CMRA HeapView

/-- Lock state: `Cinl ()` while being written, `Cinr n` with `n` readers. The `Nat` CMRA is `(ℕ, +)`. -/
abbrev LockStateR := Csum Unit Nat

abbrev NaHeapCmra (V : Type) := LockStateR × Agree (DiscreteO V)

abbrev NaHeapUR (L V : Type) [DecidableEq L] := HeapView L (NaHeapCmra V) (GMap L)

class NaHeapGS (L V : Type) [DecidableEq L] (GF : outParam BundledGFunctors) where
  na_heap_inG : ElemG GF (constOF (NaHeapUR L V))
  naHeapName : GName

class NaHeapGpreS (L V : Type) [DecidableEq L] (GF : BundledGFunctors) where
  na_heap_preG_inG : ElemG GF (constOF (NaHeapUR L V))

attribute [reducible, instance] NaHeapGS.na_heap_inG NaHeapGpreS.na_heap_preG_inG

inductive LockState where
  | WSt
  | RSt (n : Nat)
deriving DecidableEq

export LockState (WSt RSt)

def toLockStateR : LockState → LockStateR
  | RSt n => .inr n
  | WSt => .inl ()

/-- `lockStateAdd lk n'` adds `n'` readers to a reader lock state. -/
def lockStateAdd : LockState → Nat → LockState
  | RSt n, n' => RSt (n + n')
  | WSt, _ => WSt

@[simp] theorem lockStateAdd_RSt (n n' : Nat) : lockStateAdd (RSt n) n' = RSt (n + n') := rfl
@[simp] theorem lockStateAdd_WSt (n' : Nat) : lockStateAdd WSt n' = WSt := rfl

def toNaHeap {L V LK : Type} [DecidableEq L] (tls : LK → LockState) (σ : GMap L (LK × V)) :
    GMap L (NaHeapCmra V) :=
  GMap.fmap (fun v => (toLockStateR (tls v.1), toAgree ⟨v.2⟩)) σ

section definitions
variable {L V : Type} [DecidableEq L] {GF : BundledGFunctors} [hG : NaHeapGS L V GF]
variable {LK : Type} (tls : LK → LockState)

def naHeapPointstoSt (st : LockState) (l : L) (dq : DFrac) (v : V) : IProp GF :=
  iOwn (E := hG.na_heap_inG) hG.naHeapName (Frag (H := GMap L) l dq ((toLockStateR st, toAgree ⟨v⟩) : NaHeapCmra V))

def naHeapPointsto (l : L) (dq : DFrac) (v : V) : IProp GF :=
  naHeapPointstoSt (RSt 0) l dq v

def naHeapCtx (σ : GMap L (LK × V)) : IProp GF :=
  iOwn (E := hG.na_heap_inG) hG.naHeapName (Auth (H := GMap L) (.own 1) (toNaHeap tls σ))

end definitions

/-! ## CMRA facts -/

instance lockStateR_total : IsTotal LockStateR where
  total x := by cases x <;> exact ⟨_, rfl⟩

section cmra_facts
variable {L V : Type} [DecidableEq L]
example : CMRA.Discrete (NaHeapCmra V) := inferInstance
example : IsTotal (NaHeapCmra V) := inferInstance
example : OFE.Discrete (NaHeapUR L V) := inferInstance
example (x : NaHeapUR L V) : OFE.DiscreteE x := inferInstance

variable {LK : Type} (tls : LK → LockState)

@[simp] theorem lookup_to_na_heap (σ : GMap L (LK × V)) (l : L) :
    Std.PartialMap.get? (toNaHeap tls σ) l =
      (σ !! l).map (fun v => (toLockStateR (tls v.1), toAgree ⟨v.2⟩)) := rfl

theorem toNaHeap_insert (σ : GMap L (LK × V)) (l : L) (x : LK) (v : V) :
    toNaHeap tls (<[l := (x, v)]> σ) =
      <[l := (toLockStateR (tls x), toAgree ⟨v⟩)]> (toNaHeap tls σ) := by
  apply GMap.ext; intro k
  simp only [toNaHeap, GMap.lookup_fmap, GMap.lookup_insert_eq_iff]
  split <;> rfl

theorem toLockStateR_inj {st st' : LockState} (h : toLockStateR st = toLockStateR st') :
    st = st' := by
  cases st <;> cases st' <;> simp_all [toLockStateR]

theorem toLockStateR_valid (st : LockState) : ✓ toLockStateR st := by
  cases st <;> trivial

theorem naHeapCmra_valid (st : LockState) (v : V) :
    ✓ ((toLockStateR st, toAgree ⟨v⟩) : NaHeapCmra V) :=
  ⟨toLockStateR_valid st, Agree.toAgree_valid⟩

theorem na_heap_lookup_valid {σ : GMap L (LK × V)} {l : L} {q : DFrac} {lk : LockState} {v : V}
    (H : ✓ (Auth (H := GMap L) (.own 1) (toNaHeap tls σ) •
      Frag (H := GMap L) l q ((toLockStateR lk, toAgree ⟨v⟩) : NaHeapCmra V))) :
    ∃ (ls' : LK) (n' : Nat), σ !! l = some (ls', v) ∧
      tls ls' = lockStateAdd lk n' := by
  obtain ⟨v', _, _, Hl, _, Hinc⟩ := auth_op_frag_valid_total_discrete_iff H
  rw [lookup_to_na_heap] at Hl
  cases hσ : σ !! l with
  | none => simp [hσ] at Hl
  | some p =>
    obtain ⟨ls'', v''⟩ := p
    simp only [hσ, Option.map_some, Option.some.injEq] at Hl
    subst Hl
    obtain ⟨Hinc1, Hinc2⟩ := Prod.inc_def.mp Hinc
    have hv : v = v'' := congrArg DiscreteO.car (Agree.toAgree_included.mp Hinc2)
    subst hv
    cases lk with
    | WSt =>
      cases h : tls ls'' with
      | WSt => exact ⟨ls'', 0, rfl, h⟩
      | RSt m =>
        simp only [h, toLockStateR] at Hinc1
        rcases Csum.included.mp Hinc1 with h' | ⟨_, _, _, h', _⟩ | ⟨_, _, h', _, _⟩ <;> cases h'
    | RSt n =>
      cases h : tls ls'' with
      | WSt =>
        simp only [h, toLockStateR] at Hinc1
        rcases Csum.included.mp Hinc1 with h' | ⟨_, _, h', _, _⟩ | ⟨_, _, _, h', _⟩ <;> cases h'
      | RSt m =>
        simp only [h, toLockStateR] at Hinc1
        obtain ⟨z, hz⟩ := Csum.inr_included.mp Hinc1
        exact ⟨ls'', z, rfl, by simp only [h]; exact congrArg RSt hz⟩

theorem na_heap_lookup_valid_1 {σ : GMap L (LK × V)} {l : L} {lk : LockState} {v : V}
    (H : ✓ (Auth (H := GMap L) (.own 1) (toNaHeap tls σ) •
      Frag (H := GMap L) l (.own 1) ((toLockStateR lk, toAgree ⟨v⟩) : NaHeapCmra V))) :
    ∃ ls', σ !! l = some (ls', v) ∧ tls ls' = lk := by
  obtain ⟨_, _, Hl⟩ := auth_op_frag_one_valid_iff.mp H
  rw [lookup_to_na_heap] at Hl
  cases hσ : σ !! l with
  | none => simp [hσ] at Hl
  | some p =>
    obtain ⟨ls'', v''⟩ := p
    simp only [hσ, Option.map_some, Option.some.injEq, Prod.mk.injEq] at Hl
    obtain ⟨h1, h2⟩ := Hl
    have hv : v'' = v := congrArg DiscreteO.car (Agree.toAgree_inj h2)
    subst hv
    exact ⟨ls'', rfl, toLockStateR_inj h1⟩

end cmra_facts

instance nat_zero_coreId : CMRA.CoreId (0 : Nat) := ⟨rfl⟩

/-! ## Points-to facts -/

section na_heap
variable {L V : Type} [DecidableEq L] {GF : BundledGFunctors} [hG : NaHeapGS L V GF]
variable {LK : Type} (tls : LK → LockState)

open ProofMode

instance naHeapPointstoSt_timeless (st : LockState) (l : L) (dq : DFrac) (v : V) :
    Timeless (naHeapPointstoSt (hG := hG) st l dq v) := by
  unfold naHeapPointstoSt; infer_instance

instance naHeapPointsto_timeless (l : L) (dq : DFrac) (v : V) :
    Timeless (naHeapPointsto (hG := hG) l dq v) := by
  unfold naHeapPointsto; infer_instance

instance naHeapPointsto_persistent (l : L) (v : V) :
    Persistent (naHeapPointsto (hG := hG) l .discard v) := by
  unfold naHeapPointsto naHeapPointstoSt toLockStateR; infer_instance

theorem naHeapPointsto_persist (l : L) (dq : DFrac) (v : V) :
    naHeapPointsto (hG := hG) l dq v ⊢ |==> naHeapPointsto l .discard v := by
  unfold naHeapPointsto naHeapPointstoSt
  exact iOwn_update update_frag_discard

theorem naHeapPointstoSt_op (st : LockState) (l : L) (dp dq : DFrac) (v : V)
    (hst : toLockStateR st • toLockStateR st = toLockStateR st) :
    naHeapPointstoSt (hG := hG) st l (dp • dq) v ⊣⊢
      naHeapPointstoSt st l dp v ∗ naHeapPointstoSt st l dq v := by
  unfold naHeapPointstoSt
  have hx : ((toLockStateR st, toAgree (DiscreteO.mk v)) : NaHeapCmra V) •
      ((toLockStateR st, toAgree (DiscreteO.mk v)) : NaHeapCmra V) =
      ((toLockStateR st, toAgree (DiscreteO.mk v)) : NaHeapCmra V) :=
    Prod.ext hst Agree.idemp
  refine .trans (.of_eq ?_) iOwn_op
  rw [← frag_op_eqv, hx]

instance naHeapPointsto_dfractional (l : L) (v : V) :
    DFractional (fun dq => naHeapPointsto (hG := hG) l dq v) where
  dfractional dp dq := naHeapPointstoSt_op (RSt 0) l dp dq v rfl
  dfractional_persistent := naHeapPointsto_persistent l v
  dfractional_persist dq := naHeapPointsto_persist l dq v

instance naHeapPointsto_as_dfractional (l : L) (dq : DFrac) (v : V) :
    AsDFractional (naHeapPointsto (hG := hG) l dq v) (fun dq => naHeapPointsto l dq v) dq :=
  ⟨.rfl, naHeapPointsto_dfractional l v⟩

instance naHeapPointsto_fractional (l : L) (v : V) :
    Fractional (fun q => naHeapPointsto (hG := hG) l (.own q) v) :=
  fractional_of_dfractional (fun dq => naHeapPointsto l dq v)

instance naHeapPointsto_as_fractional (l : L) (q : Qp) (v : V) :
    AsFractional (naHeapPointsto (hG := hG) l (.own q) v) ioΦ
      (fun q => naHeapPointsto l (.own q) v) ioq q :=
  ⟨.rfl, naHeapPointsto_fractional l v⟩

instance naHeapPointstoSt_fractional (l : L) (v : V) :
    Fractional (fun q => naHeapPointstoSt (hG := hG) WSt l (.own q) v) where
  fractional p q := naHeapPointstoSt_op WSt l (.own p) (.own q) v rfl

theorem naHeapPointstoSt_valid_2 (st1 st2 : LockState) (l : L) (dq1 dq2 : DFrac) (v1 v2 : V) :
    naHeapPointstoSt (hG := hG) st1 l dq1 v1 ∗ naHeapPointstoSt st2 l dq2 v2 ⊢
      ⌜✓ (dq1 • dq2) ∧ ✓ (toLockStateR st1 • toLockStateR st2) ∧ v1 = v2⌝ := by
  unfold naHeapPointstoSt
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %H
  ipureintro
  obtain ⟨h1, h2, h3⟩ := frag_op_valid_iff.mp H
  exact ⟨h1, h2, congrArg DiscreteO.car (toAgree_op_valid_iff_eq.mp h3)⟩

instance naHeapPointsto_combine_sep_gives (l : L) (dq1 dq2 : DFrac) (v1 v2 : V) :
    CombineSepGives (naHeapPointsto (hG := hG) l dq1 v1) (naHeapPointsto l dq2 v2)
      iprop(⌜✓ (dq1 • dq2) ∧ v1 = v2⌝) where
  combine_sep_gives := by
    unfold naHeapPointsto
    iintro H
    icases naHeapPointstoSt_valid_2 _ _ l dq1 dq2 v1 v2 $$ H with %⟨h1, _, h3⟩
    imodintro; ipureintro; exact ⟨h1, h3⟩

theorem naHeapPointstoSt_agree (st1 st2 : LockState) (l : L) (dq1 dq2 : DFrac) (v1 v2 : V) :
    naHeapPointstoSt (hG := hG) st1 l dq1 v1 ∗ naHeapPointstoSt st2 l dq2 v2 ⊢ ⌜v1 = v2⌝ := by
  iintro H
  icases naHeapPointstoSt_valid_2 _ _ l dq1 dq2 v1 v2 $$ H with %⟨_, _, h3⟩
  ipureintro; exact h3

theorem naHeapPointstoSt_WSt_agree (st : LockState) (l : L) (dq1 dq2 : DFrac) (v1 v2 : V) :
    naHeapPointstoSt (hG := hG) WSt l dq1 v1 ∗ naHeapPointstoSt st l dq2 v2 ⊢ ⌜WSt = st⌝ := by
  iintro H
  icases naHeapPointstoSt_valid_2 _ _ l dq1 dq2 v1 v2 $$ H with %⟨_, h2, _⟩
  ipureintro
  cases st with
  | WSt => rfl
  | RSt n => exact h2.elim

theorem naHeapPointsto_agree (l : L) (dq1 dq2 : DFrac) (v1 v2 : V) :
    naHeapPointsto (hG := hG) l dq1 v1 ∗ naHeapPointsto l dq2 v2 ⊢ ⌜v1 = v2⌝ :=
  naHeapPointstoSt_agree _ _ l dq1 dq2 v1 v2

theorem naHeapPointstoSt_valid (st : LockState) (l : L) (dq : DFrac) (v : V) :
    naHeapPointstoSt (hG := hG) st l dq v ⊢ ⌜✓ dq⌝ := by
  unfold naHeapPointstoSt
  refine iOwn_cmraValid.trans ?_
  iintro %h
  ipureintro
  exact (frag_valid_iff.mp h).left

theorem naHeapPointstoSt_frac_valid (st : LockState) (l : L) (q : Qp) (v : V) :
    naHeapPointstoSt (hG := hG) st l (.own q) v ⊢ ⌜q.val ≤ 1⌝ :=
  naHeapPointstoSt_valid st l (.own q) v

theorem naHeapPointsto_valid (l : L) (dq : DFrac) (v : V) :
    naHeapPointsto (hG := hG) l dq v ⊢ ⌜✓ dq⌝ :=
  naHeapPointstoSt_valid _ l dq v

theorem naHeapPointsto_frac_valid (l : L) (q : Qp) (v : V) :
    naHeapPointsto (hG := hG) l (.own q) v ⊢ ⌜q.val ≤ 1⌝ :=
  naHeapPointstoSt_valid _ l (.own q) v

theorem naHeapPointstoSt_rd_frac (l : L) (n n' : Nat) (q q' : Qp) (v : V) :
    naHeapPointstoSt (hG := hG) (RSt (n + n')) l (.own (q + q')) v ⊣⊢
      naHeapPointstoSt (RSt n) l (.own q) v ∗ naHeapPointstoSt (RSt n') l (.own q') v := by
  unfold naHeapPointstoSt
  have hx : ((toLockStateR (RSt n), toAgree (DiscreteO.mk v)) : NaHeapCmra V) •
      ((toLockStateR (RSt n'), toAgree (DiscreteO.mk v)) : NaHeapCmra V) =
      ((toLockStateR (RSt (n + n')), toAgree (DiscreteO.mk v)) : NaHeapCmra V) :=
    Prod.ext rfl Agree.idemp
  refine .trans (.of_eq ?_) iOwn_op
  rw [← frag_add_op_eqv, hx]

/-! ## The heap context -/

theorem na_heap_init [hpre : NaHeapGpreS L V GF] (σ : GMap L (LK × V)) :
    ⊢@{IProp GF} |==> ∃ hG : NaHeapGS L V GF, naHeapCtx (hG := hG) tls σ := by
  unfold naHeapCtx
  imod iOwn_alloc (E := hpre.na_heap_preG_inG)
    (Auth (H := GMap L) (.own 1) (toNaHeap tls σ)) auth_one_valid with ⟨%γ, H⟩
  imodintro
  iexists ⟨hpre.na_heap_preG_inG, γ⟩
  iexact H

theorem naHeapPointsto_lookup (σ : GMap L (LK × V)) (l : L) (lk : LockState) (q : DFrac)
    (v : V) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointstoSt lk l q v -∗
      ⌜∃ (ls' : LK) (n' : Nat), σ !! l = some (ls', v) ∧
        tls ls' = lockStateAdd lk n'⌝ := by
  unfold naHeapCtx naHeapPointstoSt
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact na_heap_lookup_valid tls H

theorem naHeapPointsto_lookup_1 (σ : GMap L (LK × V)) (l : L) (lk : LockState) (v : V) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointstoSt lk l (.own 1) v -∗
      ⌜∃ ls', σ !! l = some (ls', v) ∧ tls ls' = lk⌝ := by
  unfold naHeapCtx naHeapPointstoSt
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact na_heap_lookup_valid_1 tls H

theorem na_heap_alloc (σ : GMap L (LK × V)) (l : L) (v : V) (lk : LK)
    (Hσl : σ !! l = none) (Hread : tls lk = RSt 0) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ ==∗
      naHeapCtx tls (<[l := (lk, v)]> σ) ∗ naHeapPointsto l (.own 1) v := by
  unfold naHeapCtx naHeapPointsto naHeapPointstoSt
  have hupd : Auth (H := GMap L) (.own 1) (toNaHeap tls σ) ~~>
      Auth (H := GMap L) (.own 1) (toNaHeap tls (<[l := (lk, v)]> σ)) •
        Frag (H := GMap L) l (.own 1)
          ((toLockStateR (RSt 0), toAgree (DiscreteO.mk v)) : NaHeapCmra V) := by
    rw [toNaHeap_insert, Hread]
    exact update_one_alloc (by simp [Hσl]) DFrac.valid_own_one (naHeapCmra_valid _ _)
  iintro H
  iapply (BIUpdate.mono iOwn_op.1)
  iapply (iOwn_update hupd) $$ H

theorem na_heap_read_vs (σ : GMap L (LK × V)) (n1 n2 nf : Nat) (l : L) (q : DFrac) (v : V)
    (lk lk' : LK) (Hσv : σ !! l = some (lk, v)) (Hr1 : tls lk = RSt (n1 + nf))
    (Hr2 : tls lk' = RSt (n2 + nf)) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointstoSt (RSt n1) l q v ==∗
      naHeapCtx tls (<[l := (lk', v)]> σ) ∗ naHeapPointstoSt (RSt n2) l q v := by
  unfold naHeapCtx naHeapPointstoSt
  have hupd : Auth (H := GMap L) (.own 1) (toNaHeap tls σ) •
        Frag (H := GMap L) l q
          ((toLockStateR (RSt n1), toAgree (DiscreteO.mk v)) : NaHeapCmra V) ~~>
      Auth (H := GMap L) (.own 1) (toNaHeap tls (<[l := (lk', v)]> σ)) •
        Frag (H := GMap L) l q
          ((toLockStateR (RSt n2), toAgree (DiscreteO.mk v)) : NaHeapCmra V) := by
    rw [toNaHeap_insert, Hr2]
    refine update_of_local_update (mv := ((toLockStateR (RSt (n1 + nf)),
      toAgree (DiscreteO.mk v)) : NaHeapCmra V)) (by simp [Hσv, Hr1]) ?_
    refine LocalUpdate.prod_1 _ _ (Csum.local_update_r ?_)
    refine (local_update_unital_discrete _ _ _ _).mpr fun z _ h => ⟨trivial, ?_⟩
    change n1 + nf = n1 + z at h
    change n2 + nf = n2 + z
    omega
  iintro H1 H2
  iapply (BIUpdate.mono iOwn_op.1)
  iapply (iOwn_update hupd)
  iapply iOwn_op.2
  iframe

theorem na_heap_write_vs (σ : GMap L (LK × V)) (st1 st2 : LK) (l : L) (v v' : V) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointstoSt (tls st1) l (.own 1) v ==∗
      naHeapCtx tls (<[l := (st2, v')]> σ) ∗ naHeapPointstoSt (tls st2) l (.own 1) v' := by
  unfold naHeapCtx naHeapPointstoSt
  have hupd : Auth (H := GMap L) (.own 1) (toNaHeap tls σ) •
        Frag (H := GMap L) l (.own 1)
          ((toLockStateR (tls st1), toAgree (DiscreteO.mk v)) : NaHeapCmra V) ~~>
      Auth (H := GMap L) (.own 1) (toNaHeap tls (<[l := (st2, v')]> σ)) •
        Frag (H := GMap L) l (.own 1)
          ((toLockStateR (tls st2), toAgree (DiscreteO.mk v')) : NaHeapCmra V) := by
    rw [toNaHeap_insert]
    exact update_replace (naHeapCmra_valid _ _)
  iintro H1 H2
  iapply (BIUpdate.mono iOwn_op.1)
  iapply (iOwn_update hupd)
  iapply iOwn_op.2
  iframe

theorem na_heap_write_lookup (σ : GMap L (LK × V)) (l : L) (q : DFrac) (v : V) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointstoSt WSt l q v -∗
      ⌜∃ lk, σ !! l = some (lk, v) ∧ tls lk = WSt⌝ := by
  iintro Hσ Hmt
  icases naHeapPointsto_lookup tls σ l WSt q v $$ Hσ Hmt with %⟨lk, _, H1, H2⟩
  ipureintro; exact ⟨lk, H1, H2⟩

theorem na_heap_read' (σ : GMap L (LK × V)) (n : Nat) (l : L) (q : DFrac) (v : V) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointstoSt (RSt n) l q v -∗
      ⌜∃ lk n', σ !! l = some (lk, v) ∧ tls lk = RSt n' ∧ n ≤ n'⌝ := by
  iintro Hσ Hmt
  icases naHeapPointsto_lookup tls σ l (RSt n) q v $$ Hσ Hmt with %⟨lk, n', H1, H2⟩
  ipureintro; exact ⟨lk, n + n', H1, H2, Nat.le_add_right _ _⟩

theorem na_heap_read (σ : GMap L (LK × V)) (l : L) (q : DFrac) (v : V) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointsto l q v -∗
      ⌜∃ lk n, σ !! l = some (lk, v) ∧ tls lk = RSt n⌝ := by
  unfold naHeapPointsto
  iintro Hσ Hmt
  icases na_heap_read' tls σ 0 l q v $$ Hσ Hmt with %⟨lk, n', H1, H2, _⟩
  ipureintro; exact ⟨lk, n', H1, H2⟩

theorem na_heap_read_1' (σ : GMap L (LK × V)) (n : Nat) (l : L) (v : V) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointstoSt (RSt n) l (.own 1) v -∗
      ⌜∃ lk, σ !! l = some (lk, v) ∧ tls lk = RSt n⌝ :=
  naHeapPointsto_lookup_1 tls σ l (RSt n) v

theorem na_heap_read_1 (σ : GMap L (LK × V)) (l : L) (v : V) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointsto l (.own 1) v -∗
      ⌜∃ lk, σ !! l = some (lk, v) ∧ tls lk = RSt 0⌝ :=
  na_heap_read_1' tls σ 0 l v

/-- `rl` updates a lock state to one with an additional reader. -/
def IsReadLock (rl : LK → LK) : Prop :=
  ∀ lk n, tls lk = RSt n → tls (rl lk) = RSt (n + 1)

def IsReadUnlock (url : LK → LK) : Prop :=
  ∀ lk n, tls lk = RSt (n + 1) → tls (url lk) = RSt n

theorem na_heap_read_prepare' (rl : LK → LK) (σ : GMap L (LK × V)) (l : L) (n : Nat)
    (q : DFrac) (v : V) (Hrl : IsReadLock tls rl) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointstoSt (RSt n) l q v ==∗
      ∃ lk n', ⌜σ !! l = some (lk, v) ∧ tls lk = RSt n'⌝ ∗
        naHeapCtx tls (<[l := (rl lk, v)]> σ) ∗ naHeapPointstoSt (RSt (n + 1)) l q v := by
  iintro Hσ Hmt
  icases naHeapPointsto_lookup tls σ l (RSt n) q v $$ Hσ Hmt with %⟨lk, n', Hσl, Hlk⟩
  simp only [lockStateAdd_RSt] at Hlk
  imod na_heap_read_vs tls σ n (n + 1) n' l q v lk (rl lk) Hσl Hlk
    (by rw [Hrl lk _ Hlk]; congr 1; omega) $$ Hσ Hmt with ⟨Hσ, Hmt⟩
  imodintro
  iexists lk, n + n'
  iframe
  ipureintro; exact ⟨Hσl, Hlk⟩

theorem na_heap_read_prepare (rl : LK → LK) (σ : GMap L (LK × V)) (l : L) (dq : DFrac) (v : V)
    (Hrl : IsReadLock tls rl) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointsto l dq v ==∗
      ∃ lk n, ⌜σ !! l = some (lk, v) ∧ tls lk = RSt n⌝ ∗
        naHeapCtx tls (<[l := (rl lk, v)]> σ) ∗ naHeapPointstoSt (RSt 1) l dq v :=
  na_heap_read_prepare' tls rl σ l 0 dq v Hrl

theorem na_heap_read_finish_vs' (url : LK → LK) (l : L) (n : Nat) (q : DFrac) (v : V)
    (Hurl : IsReadUnlock tls url) :
    ⊢@{IProp GF} naHeapPointstoSt (hG := hG) (RSt (n + 1)) l q v -∗
      ∀ σ2, naHeapCtx tls σ2 ==∗ ∃ lk n',
        ⌜σ2 !! l = some (lk, v) ∧ tls lk = RSt (n' + 1)⌝ ∗
        naHeapCtx tls (<[l := (url lk, v)]> σ2) ∗ naHeapPointstoSt (RSt n) l q v := by
  iintro Hmt %σ2 Hσ
  icases naHeapPointsto_lookup tls σ2 l (RSt (n + 1)) q v $$ Hσ Hmt with %⟨lk, n', Hσl, Hlk⟩
  simp only [lockStateAdd_RSt] at Hlk
  imod na_heap_read_vs tls σ2 (n + 1) n n' l q v lk (url lk) Hσl Hlk
    (by rw [Hurl lk (n + n') (by rw [Hlk]; congr 1; omega)]) $$ Hσ Hmt with ⟨Hσ, Hmt⟩
  imodintro
  iexists lk, n + n'
  iframe
  ipureintro; exact ⟨Hσl, by rw [Hlk]; congr 1; omega⟩

theorem na_heap_read_finish_vs (url : LK → LK) (l : L) (q : DFrac) (v : V)
    (Hurl : IsReadUnlock tls url) :
    ⊢@{IProp GF} naHeapPointstoSt (hG := hG) (RSt 1) l q v -∗
      ∀ σ2, naHeapCtx tls σ2 ==∗ ∃ lk n,
        ⌜σ2 !! l = some (lk, v) ∧ tls lk = RSt (n + 1)⌝ ∗
        naHeapCtx tls (<[l := (url lk, v)]> σ2) ∗ naHeapPointsto l q v :=
  na_heap_read_finish_vs' tls url l 0 q v Hurl

theorem na_heap_read_na (rl url : LK → LK) (σ : GMap L (LK × V)) (l : L) (q : DFrac) (v : V)
    (Hrl : IsReadLock tls rl) (Hurl : IsReadUnlock tls url) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointsto l q v ==∗
      ∃ lk n, ⌜σ !! l = some (lk, v) ∧ tls lk = RSt n⌝ ∗
        naHeapCtx tls (<[l := (rl lk, v)]> σ) ∗
        (∀ σ2, naHeapCtx tls σ2 ==∗ ∃ lk n2,
          ⌜σ2 !! l = some (lk, v) ∧ tls lk = RSt (n2 + 1)⌝ ∗
          naHeapCtx tls (<[l := (url lk, v)]> σ2) ∗ naHeapPointsto l q v) := by
  iintro Hσ Hmt
  imod na_heap_read_prepare tls rl σ l q v Hrl $$ Hσ Hmt with ⟨%lk, %n, %Heq, Hσ, Hmt⟩
  imodintro
  iexists lk, n
  iframe
  isplitr
  · ipureintro; exact Heq
  iapply na_heap_read_finish_vs tls url l q v Hurl $$ Hmt

theorem na_heap_write (σ : GMap L (LK × V)) (l : L) (lk : LK) (v v' : V)
    (Hread_lk : tls lk = RSt 0) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointsto l (.own 1) v ==∗
      naHeapCtx tls (<[l := (lk, v')]> σ) ∗ naHeapPointsto l (.own 1) v' := by
  unfold naHeapPointsto
  iintro Hσ Hmt
  icases na_heap_read_1' tls σ 0 l v $$ Hσ Hmt with %⟨lk0, Hσl, Hlk0⟩
  have Hvs := na_heap_write_vs (hG := hG) tls σ lk0 lk l v v'
  rw [Hlk0, Hread_lk] at Hvs
  iapply Hvs $$ Hσ Hmt

def TlsWriteUnique : Prop :=
  ∀ lk1 lk2, tls lk1 = WSt → tls lk2 = WSt → lk1 = lk2

theorem na_heap_write_prepare (σ : GMap L (LK × V)) (l : L) (v : V) (lkw : LK)
    (Hwrite : tls lkw = WSt) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointsto l (.own 1) v ==∗
      ∃ lk1, ⌜σ !! l = some (lk1, v) ∧ tls lk1 = RSt 0⌝ ∗
        naHeapCtx tls (<[l := (lkw, v)]> σ) ∗ naHeapPointstoSt WSt l (.own 1) v := by
  unfold naHeapPointsto
  iintro Hσ Hmt
  icases na_heap_read_1' tls σ 0 l v $$ Hσ Hmt with %⟨lkr, Hσl, Hread⟩
  have Hvs := na_heap_write_vs (hG := hG) tls σ lkr lkw l v v
  rw [Hread, Hwrite] at Hvs
  imod Hvs $$ Hσ Hmt with ⟨Hσ, Hmt⟩
  imodintro
  iexists lkr
  iframe
  ipureintro; exact ⟨Hσl, Hread⟩

theorem na_heap_write_finish_vs (l : L) (v v' : V) (lk' : LK) (Hread : tls lk' = RSt 0) :
    ⊢@{IProp GF} naHeapPointstoSt (hG := hG) WSt l (.own 1) v -∗
      ∀ σ2, naHeapCtx tls σ2 ==∗ ∃ lkw, ⌜σ2 !! l = some (lkw, v) ∧ tls lkw = WSt⌝ ∗
        naHeapCtx tls (<[l := (lk', v')]> σ2) ∗ naHeapPointsto l (.own 1) v' := by
  unfold naHeapPointsto
  iintro Hmt %σ2 Hσ
  icases naHeapPointsto_lookup tls σ2 l WSt (.own 1) v $$ Hσ Hmt with %⟨lk2, _, Hσl, Hlk'⟩
  simp only [lockStateAdd_WSt] at Hlk'
  have Hvs := na_heap_write_vs (hG := hG) tls σ2 lk2 lk' l v v'
  rw [Hread, Hlk'] at Hvs
  imod Hvs $$ Hσ Hmt with ⟨Hσ, Hmt⟩
  imodintro
  iexists lk2
  iframe
  ipureintro; exact ⟨Hσl, Hlk'⟩

theorem na_heap_write_na (σ : GMap L (LK × V)) (l : L) (v v' : V) (lkw : LK)
    (Huniq : TlsWriteUnique tls) (Hwrite : tls lkw = WSt) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ -∗ naHeapPointsto l (.own 1) v ==∗
      ∃ lk1, ⌜σ !! l = some (lk1, v) ∧ tls lk1 = RSt 0⌝ ∗
        naHeapCtx tls (<[l := (lkw, v)]> σ) ∗
        (∀ σ2, naHeapCtx tls σ2 ==∗ ⌜σ2 !! l = some (lkw, v)⌝ ∗
          naHeapCtx tls (<[l := (lk1, v')]> σ2) ∗ naHeapPointsto l (.own 1) v') := by
  iintro Hσ Hmt
  imod na_heap_write_prepare tls σ l v lkw Hwrite $$ Hσ Hmt with ⟨%lk1, %Heq, Hσ, Hmt⟩
  imodintro
  iexists lk1
  iframe
  isplitr
  · ipureintro; exact Heq
  iintro %σ2 Hσ
  imod na_heap_write_finish_vs tls l v v' lk1 Heq.2 $$ Hmt %σ2 Hσ with ⟨%lkw', %Heq', Hσ, Hmt⟩
  imodintro
  iframe
  ipureintro
  rw [Heq'.1, Huniq lkw' lkw Heq'.2 Hwrite]

end na_heap

end Perennial
