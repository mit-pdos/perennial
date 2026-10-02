/-
Non-atomic heap. Port of `src/algebra/na_heap.v`.

A heap that supports non-atomic operations: each location carries a lock state
(`WSt` while being written, `RSt n` while `n` readers are active). Adapted from
lambda-rust by Jung et al.

Differences from the Rocq version:
* Only the value heap is kept. The meta-token (`meta_token`, `meta`) and block
  size (`na_block_size`) ghost state are dropped, since new goose does not use
  them; `na_heap_ctx` is just the authoritative heap view.
* Maps are `Perennial.gmap`.
-/
import Iris.Algebra.HeapView
import Iris.Algebra.Csum
import Iris.Algebra.Agree
import Iris.Algebra.Numbers
import Iris.Instances.IProp
import Iris.Instances.Lib.LaterCredits
import Iris.BI.Lib.Fractional
import Iris.ProofMode
import Perennial.Std.GMap
import Perennial.IrisLib.DFractional

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.Algebra Iris.Std CMRA HeapView

/-- Rocq `lock_stateR := csumR unitR natR`. The `Nat` CMRA is `(ℕ, +)`. -/
abbrev lock_stateR := Csum Unit Nat

abbrev na_heap_cmra (V : Type) := lock_stateR × Agree (DiscreteO V)

abbrev na_heapUR (L V : Type) [DecidableEq L] := HeapView L (na_heap_cmra V) (gmap L)

class na_heapGS (L V : Type) [DecidableEq L] (GF : outParam BundledGFunctors) where
  na_heap_inG : ElemG GF (constOF (na_heapUR L V))
  na_heap_name : GName

class na_heapGpreS (L V : Type) [DecidableEq L] (GF : BundledGFunctors) where
  na_heap_preG_inG : ElemG GF (constOF (na_heapUR L V))

attribute [reducible, instance] na_heapGS.na_heap_inG na_heapGpreS.na_heap_preG_inG

inductive lock_state where
  | WSt
  | RSt (n : Nat)
deriving DecidableEq

export lock_state (WSt RSt)

def to_lock_stateR : lock_state → lock_stateR
  | RSt n => .inr n
  | WSt => .inl ()

/-- `lock_state_add lk n'` adds `n'` readers to a reader lock state. -/
def lock_state_add : lock_state → Nat → lock_state
  | RSt n, n' => RSt (n + n')
  | WSt, _ => WSt

@[simp] theorem lock_state_add_RSt (n n' : Nat) : lock_state_add (RSt n) n' = RSt (n + n') := rfl
@[simp] theorem lock_state_add_WSt (n' : Nat) : lock_state_add WSt n' = WSt := rfl

def to_na_heap {L V LK : Type} [DecidableEq L] (tls : LK → lock_state) (σ : gmap L (LK × V)) :
    gmap L (na_heap_cmra V) :=
  gmap.fmap (fun v => (to_lock_stateR (tls v.1), toAgree ⟨v.2⟩)) σ

section definitions
variable {L V : Type} [DecidableEq L] {GF : BundledGFunctors} [hG : na_heapGS L V GF]
variable {LK : Type} (tls : LK → lock_state)

def na_heap_pointsto_st (st : lock_state) (l : L) (dq : DFrac) (v : V) : IProp GF :=
  iOwn (E := hG.na_heap_inG) hG.na_heap_name (Frag (H := gmap L) l dq ((to_lock_stateR st, toAgree ⟨v⟩) : na_heap_cmra V))

def na_heap_pointsto (l : L) (dq : DFrac) (v : V) : IProp GF :=
  na_heap_pointsto_st (RSt 0) l dq v

def na_heap_ctx (σ : gmap L (LK × V)) : IProp GF :=
  iOwn (E := hG.na_heap_inG) hG.na_heap_name (Auth (H := gmap L) (.own 1) (to_na_heap tls σ))

end definitions

/-! ## CMRA facts -/

instance lock_stateR_total : IsTotal lock_stateR where
  total x := by cases x <;> exact ⟨_, rfl⟩

section cmra_facts
variable {L V : Type} [DecidableEq L]
example : CMRA.Discrete (na_heap_cmra V) := inferInstance
example : IsTotal (na_heap_cmra V) := inferInstance
example : OFE.Discrete (na_heapUR L V) := inferInstance
example (x : na_heapUR L V) : OFE.DiscreteE x := inferInstance

variable {LK : Type} (tls : LK → lock_state)

@[simp] theorem lookup_to_na_heap (σ : gmap L (LK × V)) (l : L) :
    Std.PartialMap.get? (to_na_heap tls σ) l =
      (σ !! l).map (fun v => (to_lock_stateR (tls v.1), toAgree ⟨v.2⟩)) := rfl

theorem to_na_heap_insert (σ : gmap L (LK × V)) (l : L) (x : LK) (v : V) :
    to_na_heap tls (<[l := (x, v)]> σ) =
      <[l := (to_lock_stateR (tls x), toAgree ⟨v⟩)]> (to_na_heap tls σ) := by
  apply gmap.ext; intro k
  simp only [to_na_heap, gmap.lookup_fmap, gmap.lookup_insert_eq_iff]
  split <;> rfl

theorem to_lock_stateR_inj {st st' : lock_state} (h : to_lock_stateR st = to_lock_stateR st') :
    st = st' := by
  cases st <;> cases st' <;> simp_all [to_lock_stateR]

theorem to_lock_stateR_valid (st : lock_state) : ✓ to_lock_stateR st := by
  cases st <;> trivial

theorem na_heap_cmra_valid (st : lock_state) (v : V) :
    ✓ ((to_lock_stateR st, toAgree ⟨v⟩) : na_heap_cmra V) :=
  ⟨to_lock_stateR_valid st, Agree.toAgree_valid⟩

theorem na_heap_lookup_valid {σ : gmap L (LK × V)} {l : L} {q : DFrac} {lk : lock_state} {v : V}
    (H : ✓ (Auth (H := gmap L) (.own 1) (to_na_heap tls σ) •
      Frag (H := gmap L) l q ((to_lock_stateR lk, toAgree ⟨v⟩) : na_heap_cmra V))) :
    ∃ (ls' : LK) (n' : Nat), σ !! l = some (ls', v) ∧
      tls ls' = lock_state_add lk n' := by
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
        simp only [h, to_lock_stateR] at Hinc1
        rcases Csum.included.mp Hinc1 with h' | ⟨_, _, _, h', _⟩ | ⟨_, _, h', _, _⟩ <;> cases h'
    | RSt n =>
      cases h : tls ls'' with
      | WSt =>
        simp only [h, to_lock_stateR] at Hinc1
        rcases Csum.included.mp Hinc1 with h' | ⟨_, _, h', _, _⟩ | ⟨_, _, _, h', _⟩ <;> cases h'
      | RSt m =>
        simp only [h, to_lock_stateR] at Hinc1
        obtain ⟨z, hz⟩ := Csum.inr_included.mp Hinc1
        exact ⟨ls'', z, rfl, by simp only [h]; exact congrArg RSt hz⟩

theorem na_heap_lookup_valid_1 {σ : gmap L (LK × V)} {l : L} {lk : lock_state} {v : V}
    (H : ✓ (Auth (H := gmap L) (.own 1) (to_na_heap tls σ) •
      Frag (H := gmap L) l (.own 1) ((to_lock_stateR lk, toAgree ⟨v⟩) : na_heap_cmra V))) :
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
    exact ⟨ls'', rfl, to_lock_stateR_inj h1⟩

end cmra_facts

instance nat_zero_coreId : CMRA.CoreId (0 : Nat) := ⟨rfl⟩

/-! ## Points-to facts -/

section na_heap
variable {L V : Type} [DecidableEq L] {GF : BundledGFunctors} [hG : na_heapGS L V GF]
variable {LK : Type} (tls : LK → lock_state)

open ProofMode

instance na_heap_pointsto_st_timeless (st : lock_state) (l : L) (dq : DFrac) (v : V) :
    Timeless (na_heap_pointsto_st (hG := hG) st l dq v) := by
  unfold na_heap_pointsto_st; infer_instance

instance na_heap_pointsto_timeless (l : L) (dq : DFrac) (v : V) :
    Timeless (na_heap_pointsto (hG := hG) l dq v) := by
  unfold na_heap_pointsto; infer_instance

instance na_heap_pointsto_persistent (l : L) (v : V) :
    Persistent (na_heap_pointsto (hG := hG) l .discard v) := by
  unfold na_heap_pointsto na_heap_pointsto_st to_lock_stateR; infer_instance

theorem na_heap_pointsto_persist (l : L) (dq : DFrac) (v : V) :
    na_heap_pointsto (hG := hG) l dq v ⊢ |==> na_heap_pointsto l .discard v := by
  unfold na_heap_pointsto na_heap_pointsto_st
  exact iOwn_update update_frag_discard

theorem na_heap_pointsto_st_op (st : lock_state) (l : L) (dp dq : DFrac) (v : V)
    (hst : to_lock_stateR st • to_lock_stateR st = to_lock_stateR st) :
    na_heap_pointsto_st (hG := hG) st l (dp • dq) v ⊣⊢
      na_heap_pointsto_st st l dp v ∗ na_heap_pointsto_st st l dq v := by
  unfold na_heap_pointsto_st
  have hx : ((to_lock_stateR st, toAgree (DiscreteO.mk v)) : na_heap_cmra V) •
      ((to_lock_stateR st, toAgree (DiscreteO.mk v)) : na_heap_cmra V) =
      ((to_lock_stateR st, toAgree (DiscreteO.mk v)) : na_heap_cmra V) :=
    Prod.ext hst Agree.idemp
  refine .trans (.of_eq ?_) iOwn_op
  rw [← frag_op_eqv, hx]

instance na_heap_pointsto_dfractional (l : L) (v : V) :
    DFractional (fun dq => na_heap_pointsto (hG := hG) l dq v) where
  dfractional dp dq := na_heap_pointsto_st_op (RSt 0) l dp dq v rfl
  dfractional_persistent := na_heap_pointsto_persistent l v
  dfractional_persist dq := na_heap_pointsto_persist l dq v

instance na_heap_pointsto_as_dfractional (l : L) (dq : DFrac) (v : V) :
    AsDFractional (na_heap_pointsto (hG := hG) l dq v) (fun dq => na_heap_pointsto l dq v) dq :=
  ⟨.rfl, na_heap_pointsto_dfractional l v⟩

instance na_heap_pointsto_fractional (l : L) (v : V) :
    Fractional (fun q => na_heap_pointsto (hG := hG) l (.own q) v) :=
  fractional_of_dfractional (fun dq => na_heap_pointsto l dq v)

instance na_heap_pointsto_as_fractional (l : L) (q : Qp) (v : V) :
    AsFractional (na_heap_pointsto (hG := hG) l (.own q) v) ioΦ
      (fun q => na_heap_pointsto l (.own q) v) ioq q :=
  ⟨.rfl, na_heap_pointsto_fractional l v⟩

instance na_heap_pointsto_st_fractional (l : L) (v : V) :
    Fractional (fun q => na_heap_pointsto_st (hG := hG) WSt l (.own q) v) where
  fractional p q := na_heap_pointsto_st_op WSt l (.own p) (.own q) v rfl

theorem na_heap_pointsto_st_valid_2 (st1 st2 : lock_state) (l : L) (dq1 dq2 : DFrac) (v1 v2 : V) :
    na_heap_pointsto_st (hG := hG) st1 l dq1 v1 ∗ na_heap_pointsto_st st2 l dq2 v2 ⊢
      ⌜✓ (dq1 • dq2) ∧ ✓ (to_lock_stateR st1 • to_lock_stateR st2) ∧ v1 = v2⌝ := by
  unfold na_heap_pointsto_st
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %H
  ipureintro
  obtain ⟨h1, h2, h3⟩ := frag_op_valid_iff.mp H
  exact ⟨h1, h2, congrArg DiscreteO.car (toAgree_op_valid_iff_eq.mp h3)⟩

instance na_heap_pointsto_combine_sep_gives (l : L) (dq1 dq2 : DFrac) (v1 v2 : V) :
    CombineSepGives (na_heap_pointsto (hG := hG) l dq1 v1) (na_heap_pointsto l dq2 v2)
      iprop(⌜✓ (dq1 • dq2) ∧ v1 = v2⌝) where
  combine_sep_gives := by
    unfold na_heap_pointsto
    iintro H
    icases na_heap_pointsto_st_valid_2 _ _ l dq1 dq2 v1 v2 $$ H with %⟨h1, _, h3⟩
    imodintro; ipureintro; exact ⟨h1, h3⟩

theorem na_heap_pointsto_st_agree (st1 st2 : lock_state) (l : L) (dq1 dq2 : DFrac) (v1 v2 : V) :
    na_heap_pointsto_st (hG := hG) st1 l dq1 v1 ∗ na_heap_pointsto_st st2 l dq2 v2 ⊢ ⌜v1 = v2⌝ := by
  iintro H
  icases na_heap_pointsto_st_valid_2 _ _ l dq1 dq2 v1 v2 $$ H with %⟨_, _, h3⟩
  ipureintro; exact h3

theorem na_heap_pointsto_st_WSt_agree (st : lock_state) (l : L) (dq1 dq2 : DFrac) (v1 v2 : V) :
    na_heap_pointsto_st (hG := hG) WSt l dq1 v1 ∗ na_heap_pointsto_st st l dq2 v2 ⊢ ⌜WSt = st⌝ := by
  iintro H
  icases na_heap_pointsto_st_valid_2 _ _ l dq1 dq2 v1 v2 $$ H with %⟨_, h2, _⟩
  ipureintro
  cases st with
  | WSt => rfl
  | RSt n => exact h2.elim

theorem na_heap_pointsto_agree (l : L) (dq1 dq2 : DFrac) (v1 v2 : V) :
    na_heap_pointsto (hG := hG) l dq1 v1 ∗ na_heap_pointsto l dq2 v2 ⊢ ⌜v1 = v2⌝ :=
  na_heap_pointsto_st_agree _ _ l dq1 dq2 v1 v2

theorem na_heap_pointsto_st_valid (st : lock_state) (l : L) (dq : DFrac) (v : V) :
    na_heap_pointsto_st (hG := hG) st l dq v ⊢ ⌜✓ dq⌝ := by
  unfold na_heap_pointsto_st
  refine iOwn_cmraValid.trans ?_
  iintro %h
  ipureintro
  exact (frag_valid_iff.mp h).left

theorem na_heap_pointsto_st_frac_valid (st : lock_state) (l : L) (q : Qp) (v : V) :
    na_heap_pointsto_st (hG := hG) st l (.own q) v ⊢ ⌜q.val ≤ 1⌝ :=
  na_heap_pointsto_st_valid st l (.own q) v

theorem na_heap_pointsto_valid (l : L) (dq : DFrac) (v : V) :
    na_heap_pointsto (hG := hG) l dq v ⊢ ⌜✓ dq⌝ :=
  na_heap_pointsto_st_valid _ l dq v

theorem na_heap_pointsto_frac_valid (l : L) (q : Qp) (v : V) :
    na_heap_pointsto (hG := hG) l (.own q) v ⊢ ⌜q.val ≤ 1⌝ :=
  na_heap_pointsto_st_valid _ l (.own q) v

theorem na_heap_pointsto_st_rd_frac (l : L) (n n' : Nat) (q q' : Qp) (v : V) :
    na_heap_pointsto_st (hG := hG) (RSt (n + n')) l (.own (q + q')) v ⊣⊢
      na_heap_pointsto_st (RSt n) l (.own q) v ∗ na_heap_pointsto_st (RSt n') l (.own q') v := by
  unfold na_heap_pointsto_st
  have hx : ((to_lock_stateR (RSt n), toAgree (DiscreteO.mk v)) : na_heap_cmra V) •
      ((to_lock_stateR (RSt n'), toAgree (DiscreteO.mk v)) : na_heap_cmra V) =
      ((to_lock_stateR (RSt (n + n')), toAgree (DiscreteO.mk v)) : na_heap_cmra V) :=
    Prod.ext rfl Agree.idemp
  refine .trans (.of_eq ?_) iOwn_op
  rw [← frag_add_op_eqv, hx]

/-! ## The heap context -/

theorem na_heap_init [hpre : na_heapGpreS L V GF] (σ : gmap L (LK × V)) :
    ⊢@{IProp GF} |==> ∃ hG : na_heapGS L V GF, na_heap_ctx (hG := hG) tls σ := by
  unfold na_heap_ctx
  imod iOwn_alloc (E := hpre.na_heap_preG_inG)
    (Auth (H := gmap L) (.own 1) (to_na_heap tls σ)) auth_one_valid with ⟨%γ, H⟩
  imodintro
  iexists ⟨hpre.na_heap_preG_inG, γ⟩
  iexact H

theorem na_heap_pointsto_lookup (σ : gmap L (LK × V)) (l : L) (lk : lock_state) (q : DFrac)
    (v : V) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto_st lk l q v -∗
      ⌜∃ (ls' : LK) (n' : Nat), σ !! l = some (ls', v) ∧
        tls ls' = lock_state_add lk n'⌝ := by
  unfold na_heap_ctx na_heap_pointsto_st
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact na_heap_lookup_valid tls H

theorem na_heap_pointsto_lookup_1 (σ : gmap L (LK × V)) (l : L) (lk : lock_state) (v : V) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto_st lk l (.own 1) v -∗
      ⌜∃ ls', σ !! l = some (ls', v) ∧ tls ls' = lk⌝ := by
  unfold na_heap_ctx na_heap_pointsto_st
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact na_heap_lookup_valid_1 tls H

theorem na_heap_alloc (σ : gmap L (LK × V)) (l : L) (v : V) (lk : LK)
    (Hσl : σ !! l = none) (Hread : tls lk = RSt 0) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ ==∗
      na_heap_ctx tls (<[l := (lk, v)]> σ) ∗ na_heap_pointsto l (.own 1) v := by
  unfold na_heap_ctx na_heap_pointsto na_heap_pointsto_st
  have hupd : Auth (H := gmap L) (.own 1) (to_na_heap tls σ) ~~>
      Auth (H := gmap L) (.own 1) (to_na_heap tls (<[l := (lk, v)]> σ)) •
        Frag (H := gmap L) l (.own 1)
          ((to_lock_stateR (RSt 0), toAgree (DiscreteO.mk v)) : na_heap_cmra V) := by
    rw [to_na_heap_insert, Hread]
    exact update_one_alloc (by simp [Hσl]) DFrac.valid_own_one (na_heap_cmra_valid _ _)
  iintro H
  iapply (BIUpdate.mono iOwn_op.1)
  iapply (iOwn_update hupd) $$ H

theorem na_heap_read_vs (σ : gmap L (LK × V)) (n1 n2 nf : Nat) (l : L) (q : DFrac) (v : V)
    (lk lk' : LK) (Hσv : σ !! l = some (lk, v)) (Hr1 : tls lk = RSt (n1 + nf))
    (Hr2 : tls lk' = RSt (n2 + nf)) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto_st (RSt n1) l q v ==∗
      na_heap_ctx tls (<[l := (lk', v)]> σ) ∗ na_heap_pointsto_st (RSt n2) l q v := by
  unfold na_heap_ctx na_heap_pointsto_st
  have hupd : Auth (H := gmap L) (.own 1) (to_na_heap tls σ) •
        Frag (H := gmap L) l q
          ((to_lock_stateR (RSt n1), toAgree (DiscreteO.mk v)) : na_heap_cmra V) ~~>
      Auth (H := gmap L) (.own 1) (to_na_heap tls (<[l := (lk', v)]> σ)) •
        Frag (H := gmap L) l q
          ((to_lock_stateR (RSt n2), toAgree (DiscreteO.mk v)) : na_heap_cmra V) := by
    rw [to_na_heap_insert, Hr2]
    refine update_of_local_update (mv := ((to_lock_stateR (RSt (n1 + nf)),
      toAgree (DiscreteO.mk v)) : na_heap_cmra V)) (by simp [Hσv, Hr1]) ?_
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

theorem na_heap_write_vs (σ : gmap L (LK × V)) (st1 st2 : LK) (l : L) (v v' : V) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto_st (tls st1) l (.own 1) v ==∗
      na_heap_ctx tls (<[l := (st2, v')]> σ) ∗ na_heap_pointsto_st (tls st2) l (.own 1) v' := by
  unfold na_heap_ctx na_heap_pointsto_st
  have hupd : Auth (H := gmap L) (.own 1) (to_na_heap tls σ) •
        Frag (H := gmap L) l (.own 1)
          ((to_lock_stateR (tls st1), toAgree (DiscreteO.mk v)) : na_heap_cmra V) ~~>
      Auth (H := gmap L) (.own 1) (to_na_heap tls (<[l := (st2, v')]> σ)) •
        Frag (H := gmap L) l (.own 1)
          ((to_lock_stateR (tls st2), toAgree (DiscreteO.mk v')) : na_heap_cmra V) := by
    rw [to_na_heap_insert]
    exact update_replace (na_heap_cmra_valid _ _)
  iintro H1 H2
  iapply (BIUpdate.mono iOwn_op.1)
  iapply (iOwn_update hupd)
  iapply iOwn_op.2
  iframe

theorem na_heap_write_lookup (σ : gmap L (LK × V)) (l : L) (q : DFrac) (v : V) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto_st WSt l q v -∗
      ⌜∃ lk, σ !! l = some (lk, v) ∧ tls lk = WSt⌝ := by
  iintro Hσ Hmt
  icases na_heap_pointsto_lookup tls σ l WSt q v $$ Hσ Hmt with %⟨lk, _, H1, H2⟩
  ipureintro; exact ⟨lk, H1, H2⟩

theorem na_heap_read' (σ : gmap L (LK × V)) (n : Nat) (l : L) (q : DFrac) (v : V) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto_st (RSt n) l q v -∗
      ⌜∃ lk n', σ !! l = some (lk, v) ∧ tls lk = RSt n' ∧ n ≤ n'⌝ := by
  iintro Hσ Hmt
  icases na_heap_pointsto_lookup tls σ l (RSt n) q v $$ Hσ Hmt with %⟨lk, n', H1, H2⟩
  ipureintro; exact ⟨lk, n + n', H1, H2, Nat.le_add_right _ _⟩

theorem na_heap_read (σ : gmap L (LK × V)) (l : L) (q : DFrac) (v : V) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto l q v -∗
      ⌜∃ lk n, σ !! l = some (lk, v) ∧ tls lk = RSt n⌝ := by
  unfold na_heap_pointsto
  iintro Hσ Hmt
  icases na_heap_read' tls σ 0 l q v $$ Hσ Hmt with %⟨lk, n', H1, H2, _⟩
  ipureintro; exact ⟨lk, n', H1, H2⟩

theorem na_heap_read_1' (σ : gmap L (LK × V)) (n : Nat) (l : L) (v : V) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto_st (RSt n) l (.own 1) v -∗
      ⌜∃ lk, σ !! l = some (lk, v) ∧ tls lk = RSt n⌝ :=
  na_heap_pointsto_lookup_1 tls σ l (RSt n) v

theorem na_heap_read_1 (σ : gmap L (LK × V)) (l : L) (v : V) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto l (.own 1) v -∗
      ⌜∃ lk, σ !! l = some (lk, v) ∧ tls lk = RSt 0⌝ :=
  na_heap_read_1' tls σ 0 l v

/-- `rl` updates a lock state to one with an additional reader. -/
def is_read_lock (rl : LK → LK) : Prop :=
  ∀ lk n, tls lk = RSt n → tls (rl lk) = RSt (n + 1)

def is_read_unlock (url : LK → LK) : Prop :=
  ∀ lk n, tls lk = RSt (n + 1) → tls (url lk) = RSt n

theorem na_heap_read_prepare' (rl : LK → LK) (σ : gmap L (LK × V)) (l : L) (n : Nat)
    (q : DFrac) (v : V) (Hrl : is_read_lock tls rl) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto_st (RSt n) l q v ==∗
      ∃ lk n', ⌜σ !! l = some (lk, v) ∧ tls lk = RSt n'⌝ ∗
        na_heap_ctx tls (<[l := (rl lk, v)]> σ) ∗ na_heap_pointsto_st (RSt (n + 1)) l q v := by
  iintro Hσ Hmt
  icases na_heap_pointsto_lookup tls σ l (RSt n) q v $$ Hσ Hmt with %⟨lk, n', Hσl, Hlk⟩
  simp only [lock_state_add_RSt] at Hlk
  imod na_heap_read_vs tls σ n (n + 1) n' l q v lk (rl lk) Hσl Hlk
    (by rw [Hrl lk _ Hlk]; congr 1; omega) $$ Hσ Hmt with ⟨Hσ, Hmt⟩
  imodintro
  iexists lk, n + n'
  iframe
  ipureintro; exact ⟨Hσl, Hlk⟩

theorem na_heap_read_prepare (rl : LK → LK) (σ : gmap L (LK × V)) (l : L) (dq : DFrac) (v : V)
    (Hrl : is_read_lock tls rl) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto l dq v ==∗
      ∃ lk n, ⌜σ !! l = some (lk, v) ∧ tls lk = RSt n⌝ ∗
        na_heap_ctx tls (<[l := (rl lk, v)]> σ) ∗ na_heap_pointsto_st (RSt 1) l dq v :=
  na_heap_read_prepare' tls rl σ l 0 dq v Hrl

theorem na_heap_read_finish_vs' (url : LK → LK) (l : L) (n : Nat) (q : DFrac) (v : V)
    (Hurl : is_read_unlock tls url) :
    ⊢@{IProp GF} na_heap_pointsto_st (hG := hG) (RSt (n + 1)) l q v -∗
      ∀ σ2, na_heap_ctx tls σ2 ==∗ ∃ lk n',
        ⌜σ2 !! l = some (lk, v) ∧ tls lk = RSt (n' + 1)⌝ ∗
        na_heap_ctx tls (<[l := (url lk, v)]> σ2) ∗ na_heap_pointsto_st (RSt n) l q v := by
  iintro Hmt %σ2 Hσ
  icases na_heap_pointsto_lookup tls σ2 l (RSt (n + 1)) q v $$ Hσ Hmt with %⟨lk, n', Hσl, Hlk⟩
  simp only [lock_state_add_RSt] at Hlk
  imod na_heap_read_vs tls σ2 (n + 1) n n' l q v lk (url lk) Hσl Hlk
    (by rw [Hurl lk (n + n') (by rw [Hlk]; congr 1; omega)]) $$ Hσ Hmt with ⟨Hσ, Hmt⟩
  imodintro
  iexists lk, n + n'
  iframe
  ipureintro; exact ⟨Hσl, by rw [Hlk]; congr 1; omega⟩

theorem na_heap_read_finish_vs (url : LK → LK) (l : L) (q : DFrac) (v : V)
    (Hurl : is_read_unlock tls url) :
    ⊢@{IProp GF} na_heap_pointsto_st (hG := hG) (RSt 1) l q v -∗
      ∀ σ2, na_heap_ctx tls σ2 ==∗ ∃ lk n,
        ⌜σ2 !! l = some (lk, v) ∧ tls lk = RSt (n + 1)⌝ ∗
        na_heap_ctx tls (<[l := (url lk, v)]> σ2) ∗ na_heap_pointsto l q v :=
  na_heap_read_finish_vs' tls url l 0 q v Hurl

theorem na_heap_read_na (rl url : LK → LK) (σ : gmap L (LK × V)) (l : L) (q : DFrac) (v : V)
    (Hrl : is_read_lock tls rl) (Hurl : is_read_unlock tls url) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto l q v ==∗
      ∃ lk n, ⌜σ !! l = some (lk, v) ∧ tls lk = RSt n⌝ ∗
        na_heap_ctx tls (<[l := (rl lk, v)]> σ) ∗
        (∀ σ2, na_heap_ctx tls σ2 ==∗ ∃ lk n2,
          ⌜σ2 !! l = some (lk, v) ∧ tls lk = RSt (n2 + 1)⌝ ∗
          na_heap_ctx tls (<[l := (url lk, v)]> σ2) ∗ na_heap_pointsto l q v) := by
  iintro Hσ Hmt
  imod na_heap_read_prepare tls rl σ l q v Hrl $$ Hσ Hmt with ⟨%lk, %n, %Heq, Hσ, Hmt⟩
  imodintro
  iexists lk, n
  iframe
  isplitr
  · ipureintro; exact Heq
  iapply na_heap_read_finish_vs tls url l q v Hurl $$ Hmt

theorem na_heap_write (σ : gmap L (LK × V)) (l : L) (lk : LK) (v v' : V)
    (Hread_lk : tls lk = RSt 0) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto l (.own 1) v ==∗
      na_heap_ctx tls (<[l := (lk, v')]> σ) ∗ na_heap_pointsto l (.own 1) v' := by
  unfold na_heap_pointsto
  iintro Hσ Hmt
  icases na_heap_read_1' tls σ 0 l v $$ Hσ Hmt with %⟨lk0, Hσl, Hlk0⟩
  have Hvs := na_heap_write_vs (hG := hG) tls σ lk0 lk l v v'
  rw [Hlk0, Hread_lk] at Hvs
  iapply Hvs $$ Hσ Hmt

def tls_write_unique : Prop :=
  ∀ lk1 lk2, tls lk1 = WSt → tls lk2 = WSt → lk1 = lk2

theorem na_heap_write_prepare (σ : gmap L (LK × V)) (l : L) (v : V) (lkw : LK)
    (Hwrite : tls lkw = WSt) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto l (.own 1) v ==∗
      ∃ lk1, ⌜σ !! l = some (lk1, v) ∧ tls lk1 = RSt 0⌝ ∗
        na_heap_ctx tls (<[l := (lkw, v)]> σ) ∗ na_heap_pointsto_st WSt l (.own 1) v := by
  unfold na_heap_pointsto
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
    ⊢@{IProp GF} na_heap_pointsto_st (hG := hG) WSt l (.own 1) v -∗
      ∀ σ2, na_heap_ctx tls σ2 ==∗ ∃ lkw, ⌜σ2 !! l = some (lkw, v) ∧ tls lkw = WSt⌝ ∗
        na_heap_ctx tls (<[l := (lk', v')]> σ2) ∗ na_heap_pointsto l (.own 1) v' := by
  unfold na_heap_pointsto
  iintro Hmt %σ2 Hσ
  icases na_heap_pointsto_lookup tls σ2 l WSt (.own 1) v $$ Hσ Hmt with %⟨lk2, _, Hσl, Hlk'⟩
  simp only [lock_state_add_WSt] at Hlk'
  have Hvs := na_heap_write_vs (hG := hG) tls σ2 lk2 lk' l v v'
  rw [Hread, Hlk'] at Hvs
  imod Hvs $$ Hσ Hmt with ⟨Hσ, Hmt⟩
  imodintro
  iexists lk2
  iframe
  ipureintro; exact ⟨Hσl, Hlk'⟩

theorem na_heap_write_na (σ : gmap L (LK × V)) (l : L) (v v' : V) (lkw : LK)
    (Huniq : tls_write_unique tls) (Hwrite : tls lkw = WSt) :
    ⊢@{IProp GF} na_heap_ctx (hG := hG) tls σ -∗ na_heap_pointsto l (.own 1) v ==∗
      ∃ lk1, ⌜σ !! l = some (lk1, v) ∧ tls lk1 = RSt 0⌝ ∗
        na_heap_ctx tls (<[l := (lkw, v)]> σ) ∗
        (∀ σ2, na_heap_ctx tls σ2 ==∗ ⌜σ2 !! l = some (lkw, v)⌝ ∗
          na_heap_ctx tls (<[l := (lk1, v')]> σ2) ∗ na_heap_pointsto l (.own 1) v') := by
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
