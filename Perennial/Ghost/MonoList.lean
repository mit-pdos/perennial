/-
Ghost state for an append-only list, wrapping
iris-lean's `MonoList` camera. Elements (of any `Pos.Countable` type) are stored
encoded (`encodeO`), see `Perennial/Ghost/All.lean`.

- `mono_list_auth_own γ q l`: authoritative list `l`;
- `mono_list_lb_own γ l`: persistent witness that the authoritative list is at
  least `l`;
- `mono_list_idx_own γ i a`: persistent witness that index `i` is `a`.
-/
import Perennial.Ghost.Own
import Perennial.Ghost.Countable

noncomputable section

namespace Perennial
open Iris BI OFE CMRA ProofMode MonoList

variable {GF : BundledGFunctors} [AllG GF] {A : Type} [Pos.Countable A]

/-! ## List helpers -/

theorem map_encodeO_inj : ∀ {l1 l2 : List A}, l1.map encodeO = l2.map encodeO → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [encodeO_inj h.1, map_encodeO_inj h.2]

theorem map_encodeO_prefix {l1 l2 : List A} (h : l1.map encodeO <+: l2.map encodeO) :
    l1 <+: l2 := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨a, b, rfl, ha, _⟩ := List.map_eq_append_iff.mp ht.symm
  exact ⟨b, by rw [map_encodeO_inj ha]⟩

theorem prefix_getElem? {l1 l2 : List A} {i : Nat} {a : A} (h : l1 <+: l2)
    (hi : l1[i]? = some a) : l2[i]? = some a := by
  obtain ⟨t, rfl⟩ := h
  grind

/-! ## Definitions -/

def monoListAuthOwn (γ : GName) (q : Qp) (l : List A) : IProp GF :=
  own γ (MonoList.auth (DFrac.own q) (l.map encodeO))

def monoListLbOwn (γ : GName) (l : List A) : IProp GF :=
  own γ (MonoList.lb (l.map encodeO))

def monoListIdxOwn (γ : GName) (i : Nat) (a : A) : IProp GF :=
  iprop(∃ l : List A, ⌜l[i]? = some a⌝ ∗ monoListLbOwn γ l)

/-! ## Instances -/

instance monoListAuthOwn_timeless (γ : GName) (q : Qp) (l : List A) :
    Timeless (monoListAuthOwn (GF := GF) γ q l) := by
  unfold monoListAuthOwn; infer_instance
instance monoListLbOwn_timeless (γ : GName) (l : List A) :
    Timeless (monoListLbOwn (GF := GF) γ l) := by
  unfold monoListLbOwn; infer_instance
instance monoListLbOwn_persistent (γ : GName) (l : List A) :
    Persistent (monoListLbOwn (GF := GF) γ l) := by
  unfold monoListLbOwn; infer_instance
instance monoListIdxOwn_timeless (γ : GName) (i : Nat) (a : A) :
    Timeless (monoListIdxOwn (GF := GF) γ i a) := by
  unfold monoListIdxOwn; infer_instance
instance monoListIdxOwn_persistent (γ : GName) (i : Nat) (a : A) :
    Persistent (monoListIdxOwn (GF := GF) γ i a) := by
  unfold monoListIdxOwn; infer_instance

instance monoListAuthOwn_fractional (γ : GName) (l : List A) :
    Fractional (fun q => monoListAuthOwn (GF := GF) γ q l) where
  fractional p q := by
    unfold monoListAuthOwn
    rw [← (own_op γ _ _).to_eq]
    exact (congrArg (own γ) (auth_dfrac_op (.own p) (.own q) _)).to_bi

instance monoListAuthOwn_as_fractional (γ : GName) (q : Qp) (l : List A) :
    AsFractional (monoListAuthOwn (GF := GF) γ q l) ioΦ
      (fun q => monoListAuthOwn γ q l) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := monoListAuthOwn_fractional γ l

/-! ## Agreement -/

theorem monoListAuthOwn_agree (γ : GName) (q1 q2 : Qp) (l1 l2 : List A) :
    ⊢ monoListAuthOwn (GF := GF) γ q1 l1 -∗ monoListAuthOwn γ q2 l2 -∗
      ⌜q1 + q2 ≤ 1 ∧ l1 = l2⌝ := by
  unfold monoListAuthOwn
  iintro H1 H2
  icombine H1 H2 gives %Hvalid
  ipureintro
  obtain ⟨hdq, hl⟩ := (auth_dfrac_op_valid ..).mp Hvalid
  exact ⟨hdq, map_encodeO_inj hl⟩

theorem monoListAuthOwn_exclusive (γ : GName) (l1 l2 : List A) :
    ⊢ monoListAuthOwn (GF := GF) γ 1 l1 -∗ monoListAuthOwn γ 1 l2 -∗ False := by
  unfold monoListAuthOwn
  iintro H1 H2
  icombine H1 H2 gives %Hvalid
  exact ((auth_op_valid ..).mp Hvalid).elim

theorem mono_list_auth_lb_valid (γ : GName) (q : Qp) (l1 l2 : List A) :
    ⊢ monoListAuthOwn (GF := GF) γ q l1 -∗ monoListLbOwn γ l2 -∗ ⌜q ≤ 1 ∧ l2 <+: l1⌝ := by
  unfold monoListAuthOwn monoListLbOwn
  iintro H1 H2
  icombine H1 H2 gives %Hvalid
  ipureintro
  obtain ⟨hdq, hpre⟩ := (both_dfrac_valid ..).mp Hvalid
  exact ⟨hdq, map_encodeO_prefix hpre⟩

theorem mono_list_lb_valid (γ : GName) (l1 l2 : List A) :
    ⊢ monoListLbOwn (GF := GF) γ l1 -∗ monoListLbOwn γ l2 -∗ ⌜l1 <+: l2 ∨ l2 <+: l1⌝ := by
  unfold monoListLbOwn
  iintro H1 H2
  icombine H1 H2 gives %Hvalid
  ipureintro
  exact (lb_op_valid ..).mp Hvalid |>.imp map_encodeO_prefix map_encodeO_prefix

theorem mono_list_idx_agree (γ : GName) (i : Nat) (a1 a2 : A) :
    ⊢ monoListIdxOwn (GF := GF) γ i a1 -∗ monoListIdxOwn γ i a2 -∗ ⌜a1 = a2⌝ := by
  unfold monoListIdxOwn
  iintro H1 H2
  icases H1 with ⟨%l1, %Hl1, H1⟩
  icases H2 with ⟨%l2, %Hl2, H2⟩
  icases mono_list_lb_valid γ l1 l2 $$ H1 H2 with %Hpre
  ipureintro
  rcases Hpre with Hpre | Hpre
  · have := prefix_getElem? Hpre Hl1; simp_all
  · have := prefix_getElem? Hpre Hl2; simp_all

theorem mono_list_auth_idx_lookup (γ : GName) (q : Qp) (l : List A) (i : Nat) (a : A) :
    ⊢ monoListAuthOwn (GF := GF) γ q l -∗ monoListIdxOwn γ i a -∗ ⌜l[i]? = some a⌝ := by
  unfold monoListIdxOwn
  iintro H1 H2
  icases H2 with ⟨%l1, %Hl1, H2⟩
  icases mono_list_auth_lb_valid γ q l l1 $$ H1 H2 with %Hpre
  ipureintro
  exact prefix_getElem? Hpre.2 Hl1

/-! ## Snapshots -/

theorem monoListLbOwn_get (γ : GName) (q : Qp) (l : List A) :
    monoListAuthOwn (GF := GF) γ q l ⊢ monoListLbOwn γ l := by
  unfold monoListAuthOwn monoListLbOwn
  exact own_mono γ _ _ (included ..)

theorem monoListLbOwn_le {γ : GName} {l : List A} (l' : List A) (h : l' <+: l) :
    monoListLbOwn (GF := GF) γ l ⊢ monoListLbOwn γ l' := by
  unfold monoListLbOwn
  exact own_mono γ _ _ (lb_mono (h.map _))

theorem monoListIdxOwn_get {γ : GName} {l : List A} (i : Nat) (a : A) (h : l[i]? = some a) :
    ⊢ monoListLbOwn (GF := GF) γ l -∗ monoListIdxOwn γ i a := by
  unfold monoListIdxOwn
  iintro H
  iexists l
  iframe H %h

/-! ## Allocation and updates -/

theorem mono_list_own_alloc (l : List A) :
    ⊢ |==> ∃ γ, monoListAuthOwn (GF := GF) γ 1 l ∗ monoListLbOwn γ l := by
  unfold monoListAuthOwn monoListLbOwn
  imod own_alloc (●ML (l.map encodeO) • ◯ML (l.map encodeO))
    ((both_valid ..).mpr List.prefix_rfl) with ⟨%γ, H⟩
  imodintro
  iexists γ
  icases (own_op γ _ _).1 $$ H with ⟨$, $⟩

theorem monoListAuthOwn_update {γ : GName} {l : List A} (l' : List A) (h : l <+: l') :
    ⊢ monoListAuthOwn (GF := GF) γ 1 l ==∗
      monoListAuthOwn γ 1 l' ∗ monoListLbOwn γ l' := by
  iintro H
  ihave >Hauth : |==> monoListAuthOwn (GF := GF) γ 1 l' $$ [H]
  · unfold monoListAuthOwn
    iapply own_update γ _ _ (update _ (h.map _)) $$ H
  · imodintro
    ihave #Hlb := monoListLbOwn_get γ 1 l' $$ Hauth
    isplitl [Hauth]
    · iexact Hauth
    · iexact Hlb

theorem monoListAuthOwn_update_app {γ : GName} {l : List A} (l' : List A) :
    ⊢ monoListAuthOwn (GF := GF) γ 1 l ==∗
      monoListAuthOwn γ 1 (l ++ l') ∗ monoListLbOwn γ (l ++ l') :=
  monoListAuthOwn_update (l ++ l') (List.prefix_append ..)

theorem monoListLbOwn_nil (γ : GName) : ⊢ |==> monoListLbOwn (GF := GF) γ ([] : List A) := by
  unfold monoListLbOwn
  rw [List.map_nil, lb_nil]
  exact own_unit γ

theorem mono_list_lb_idx_lookup (γ : GName) (l : List A) (i : Nat) (a : A) (hi : i < l.length) :
    ⊢ monoListLbOwn (GF := GF) γ l -∗ monoListIdxOwn γ i a -∗ ⌜l[i]? = some a⌝ := by
  unfold monoListIdxOwn
  iintro H0 H1
  icases H1 with ⟨%l1, %Hl1, H1⟩
  icases mono_list_lb_valid γ l l1 $$ H0 H1 with %Hpre
  ipureintro
  rcases Hpre with ⟨t, rfl⟩ | Hpre
  · rw [List.getElem?_append_left hi] at Hl1; exact Hl1
  · exact prefix_getElem? Hpre Hl1

end Perennial
