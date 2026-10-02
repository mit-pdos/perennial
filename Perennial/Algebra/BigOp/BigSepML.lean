/-
Port of `src/algebra/big_op/big_sepML.v`.

`big_sepML Φ m l` (notation `[∗maplist] k ↦ x;v ∈ m;l, P`) relates a map `m`
and a list `l` whose elements are in bijection with the keys of `m`: there is
a map `lm` with the same keys as `m` whose values are a permutation of `l`, and
`Φ k (m !! k) (lm !! k)` holds for each key.

Differences from Rocq:
* Maps are any iris-lean `LawfulFiniteMap M K` (with `DecidableEq K`); in
  particular `Perennial.gmap`. List `delete i l` is `l.eraseIdx i`, list
  `<[i := x]> l` is `l.set i x`, and `l !! i` is `l[i]?`.
* `big_sepML` is a plain definition (no seal); `big_sepML_eq` unfolds it.
* `big_sepML_nodup` needs no `BiPureForall` (iris-lean proves `pure_forall`
  for every BI).
* The `big_sepMs` part (`bsm_maps`, `bsm_pred`, `bsm_keys_match`,
  `bsm_key_pred`, `big_sepMs` and its notation) is not ported: it is unused and
  its only lemma (`big_sepM_sepMs`) is `Abort`ed in Rocq.
-/
import Iris.BI
import Iris.BI.BigOp
import Iris.ProofMode
import Iris.Std.PartialMap
import Perennial.IrisLib.Conflicting
import Perennial.Algebra.BigOp.BigSepM

namespace Perennial

open Iris Iris.BI Iris.Std BigSepM BigSepM2 BigSepL PartialMap LawfulPartialMap LawfulFiniteMap

/-! ## List helpers -/

private theorem perm_cons_eraseIdx {α : Type _} :
    ∀ (l : List α) (i : Nat) (x : α), l[i]? = some x → l.Perm (x :: l.eraseIdx i)
  | [], _, _, h => by simp at h
  | y :: l, 0, x, h => by simp at h; subst h; simp
  | y :: l, i + 1, x, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.eraseIdx_cons_succ]
    exact ((perm_cons_eraseIdx l i x h).cons y).trans (List.Perm.swap x y _)

private theorem set_perm_cons_eraseIdx {α : Type _} :
    ∀ (l : List α) (i : Nat) (x y : α), l[i]? = some x → (l.set i y).Perm (y :: l.eraseIdx i)
  | [], _, _, _, h => by simp at h
  | z :: l, 0, _, y, _ => by simp
  | z :: l, i + 1, x, y, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.eraseIdx_cons_succ]
    exact ((set_perm_cons_eraseIdx l i x y h).cons z).trans (List.Perm.swap y z _)

/-! ## Definition -/

section def_

variable {PROP : Type _} [BI PROP]
variable {K : Type _} {M : Type u → Type _} [LawfulFiniteMap M K]
variable {V LV : Type u}

/-- Rocq `big_sepML`. -/
def big_sepML (Φ : K → V → LV → PROP) (m : M V) (l : List LV) : PROP :=
  iprop(∃ lm : M LV, ⌜l.Perm ((FiniteMap.toList lm).map Prod.snd)⌝ ∗
    [∗map] k ↦ v;lvm ∈ m;lm, Φ k v lvm)

theorem big_sepML_eq (Φ : K → V → LV → PROP) (m : M V) (l : List LV) :
    big_sepML Φ m l = iprop(∃ lm : M LV, ⌜l.Perm ((FiniteMap.toList lm).map Prod.snd)⌝ ∗
      [∗map] k ↦ v;lvm ∈ m;lm, Φ k v lvm) := rfl

end def_

/-- Rocq notation `[∗ maplist] k ↦ x ; v ∈ m ; l , P`. -/
syntax "[∗maplist] " ident " ↦ " ident ";" ident " ∈ " term ";" term ", " term : term

macro_rules
  | `([∗maplist] $k ↦ $x;$v ∈ $m;$l, $P) => `(big_sepML (fun $k $x $v => iprop($P)) $m $l)

/-! ## Lemmas -/

section bi

variable {PROP : Type _} [BI PROP] [BIAffine PROP]
variable {K : Type _} {M : Type u → Type _} [LawfulFiniteMap M K] [DecidableEq K]

section maplist

variable {V LV : Type u}

/-- `[∗map]` over the values of `lm`, as a `[∗list]` over a permutation of them. -/
private theorem bigSepM_snd_perm (P : LV → PROP) (lm : M LV) (l : List LV)
    (h : l.Perm ((FiniteMap.toList lm).map Prod.snd)) :
    ([∗map] _k ↦ lv ∈ lm, P lv) ⊣⊢ [∗list] lv ∈ l, P lv :=
  bigSepM_toList.trans <| (BiEntails.of_eq (bigSepL_map Prod.snd).symm).trans (bigSepL_perm h).symm

theorem big_sepML_proper {Φ Ψ : K → V → LV → PROP} {m : M V} {l0 l1 : List LV}
    (hΦ : ∀ k v lv, Φ k v lv ⊢ Ψ k v lv) (hl : l0.Perm l1) :
    big_sepML Φ m l0 ⊢ big_sepML Ψ m l1 := by
  unfold big_sepML
  iintro ⟨%lm, %hlm, H⟩
  iexists lm
  isplitr
  · ipureintro; exact hl.symm.trans hlm
  · iapply (bigSepM2_mono fun _ _ => hΦ _ _ _) $$ H

theorem big_sepML_empty (Φ : K → V → LV → PROP) :
    ⊢ big_sepML Φ (∅ : M V) [] := by
  unfold big_sepML
  iexists (∅ : M LV)
  isplitr
  · ipureintro
    rw [show FiniteMap.toList (∅ : M LV) = [] from LawfulFiniteMap.toList_empty]
    exact List.Perm.refl _
  · rw [(bigSepM2_empty _).to_eq]; iempintro

theorem big_sepML_insert (Φ : K → V → LV → PROP) (m : M V) (l : List LV) (k : K) (v : V)
    (lv : LV) :
    get? m k = none →
    Φ k v lv ∗ big_sepML Φ m l ⊢ big_sepML Φ (insert m k v) (lv :: l) := by
  intro hk
  unfold big_sepML
  iintro ⟨Hp, %lm, %hlm, H⟩
  ihave %hlmk := (big_sepM2_lookup_l_none Φ m lm k hk) $$ H
  iexists (insert lm k lv)
  isplitr
  · ipureintro
    exact (hlm.cons lv).trans ((toList_insert hlmk).map Prod.snd).symm
  · rw [(bigSepM2_insert hk hlmk).to_eq]
    iframe

theorem big_sepML_insert_app (Φ : K → V → LV → PROP) (m : M V) (l : List LV) (k : K) (v : V)
    (lv : LV) :
    get? m k = none →
    Φ k v lv ∗ big_sepML Φ m l ⊢ big_sepML Φ (insert m k v) (l ++ [lv]) := fun hk =>
  (big_sepML_insert Φ m l k v lv hk).trans
    (big_sepML_proper (fun _ _ _ => .rfl) (List.perm_append_singleton lv l).symm)

theorem big_sepML_delete_cons (Φ : K → V → LV → PROP) (m : M V) (l : List LV) (lv : LV) :
    big_sepML Φ m (lv :: l) ⊢
      ∃ k v, ⌜get? m k = some v⌝ ∗ Φ k v lv ∗ big_sepML Φ (delete m k) l := by
  unfold big_sepML
  iintro ⟨%lm, %hlm, H⟩
  have hmem : lv ∈ (FiniteMap.toList lm).map Prod.snd := hlm.subset List.mem_cons_self
  obtain ⟨⟨k, lv0⟩, hkl, hsnd⟩ := List.mem_map.mp hmem
  simp only at hsnd; subst hsnd
  have hk : get? lm k = some lv0 := toList_get.mp hkl
  ihave %hv := (big_sepM2_lookup_r_some Φ m lm k lv0 hk) $$ H
  obtain ⟨v, hv⟩ := hv
  icases (bigSepM2_delete hv hk).1 $$ H with ⟨Hp, H⟩
  iexists k, v
  isplitr
  · ipureintro; exact hv
  isplitl [Hp]
  · iexact Hp
  iexists (delete lm k)
  isplitr
  · ipureintro
    exact (hlm.trans ((toList_delete hk).map Prod.snd)).cons_inv
  · iexact H

theorem map_to_list_insert_overwrite (l : List LV) (i : Nat) (k : K) (lv lv' : LV) (lm : M LV) :
    l[i]? = some lv →
    get? lm k = some lv →
    l.Perm ((FiniteMap.toList lm).map Prod.snd) →
    (l.set i lv').Perm ((FiniteMap.toList (insert lm k lv')).map Prod.snd) := by
  intro h1 h2 h3
  have hd := toList_delete h2
  have hi : (FiniteMap.toList (insert lm k lv')).Perm ((k, lv') :: FiniteMap.toList (delete lm k)) :=
    toList_insert_delete.trans (toList_insert (get?_delete_eq rfl))
  have he : (l.eraseIdx i).Perm ((FiniteMap.toList (delete lm k)).map Prod.snd) :=
    ((perm_cons_eraseIdx l i lv h1).symm.trans (h3.trans (hd.map Prod.snd))).cons_inv
  exact (set_perm_cons_eraseIdx l i lv lv' h1).trans ((he.cons lv').trans (hi.map Prod.snd).symm)

theorem map_to_list_delete (l : List LV) (lm : M LV) (k : K) (i : Nat) (x : LV) :
    l[i]? = some x →
    get? lm k = some x →
    l.Perm ((FiniteMap.toList lm).map Prod.snd) →
    (l.eraseIdx i).Perm ((FiniteMap.toList (delete lm k)).map Prod.snd) := by
  intro h1 h2 h3
  exact ((perm_cons_eraseIdx l i x h1).symm.trans
    (h3.trans ((toList_delete h2).map Prod.snd))).cons_inv

theorem list_some_map_to_list (l : List LV) (i : Nat) (lv : LV) (lm : M LV) :
    l[i]? = some lv →
    l.Perm ((FiniteMap.toList lm).map Prod.snd) →
    ∃ k, get? lm k = some lv := by
  intro h1 h2
  obtain ⟨⟨k, lv0⟩, hkl, hsnd⟩ := List.mem_map.mp (h2.subset (List.mem_of_getElem? h1))
  simp only at hsnd; subst hsnd
  exact ⟨k, toList_get.mp hkl⟩

theorem map_to_list_some_list (l : List LV) (k : K) (lv : LV) (lm : M LV) :
    get? lm k = some lv →
    l.Perm ((FiniteMap.toList lm).map Prod.snd) →
    ∃ i : Nat, l[i]? = some lv := by
  intro h1 h2
  have : lv ∈ l := h2.symm.subset (List.mem_map.mpr ⟨(k, lv), toList_get.mpr h1, rfl⟩)
  exact List.mem_iff_getElem?.mp this

theorem big_sepML_delete_m (Φ : K → V → LV → PROP) (m : M V) (l : List LV) (k : K) (v : V) :
    get? m k = some v →
    big_sepML Φ m l ⊢
      ∃ i lv, ⌜l[i]? = some lv⌝ ∗ Φ k v lv ∗ big_sepML Φ (delete m k) (l.eraseIdx i) := by
  intro hm
  unfold big_sepML
  iintro ⟨%lm, %hlm, H⟩
  ihave %hx := (big_sepM2_lookup_l_some Φ m lm k v hm) $$ H
  obtain ⟨x2, hx2⟩ := hx
  icases (bigSepM2_delete hm hx2).1 $$ H with ⟨Hk, H⟩
  obtain ⟨i, hi⟩ := map_to_list_some_list l k x2 lm hx2 hlm
  iexists i, x2
  isplitr
  · ipureintro; exact hi
  isplitl [Hk]
  · iexact Hk
  iexists (delete lm k)
  isplitr
  · ipureintro; exact map_to_list_delete l lm k i x2 hi hx2 hlm
  · iexact H

theorem big_sepML_lookup_l_acc (Φ : K → V → LV → PROP) (m : M V) (l : List LV) (i : Nat)
    (lv : LV) :
    l[i]? = some lv →
    big_sepML Φ m l ⊢
      ∃ k v, ⌜get? m k = some v⌝ ∗ Φ k v lv ∗
        ∀ v' lv', Φ k v' lv' -∗ big_sepML Φ (insert m k v') (l.set i lv') := by
  intro hi
  unfold big_sepML
  iintro ⟨%lm, %hlm, H⟩
  obtain ⟨k, hk⟩ := list_some_map_to_list l i lv lm hi hlm
  ihave %hv := (big_sepM2_lookup_r_some Φ m lm k lv hk) $$ H
  obtain ⟨v, hv⟩ := hv
  icases (bigSepM2_insert_acc hv hk) $$ H with ⟨Hx, H⟩
  iexists k, v
  isplitr
  · ipureintro; exact hv
  isplitl [Hx]
  · iexact Hx
  iintro %v' %lv' Hx
  iexists (insert lm k lv')
  isplitr
  · ipureintro; exact map_to_list_insert_overwrite l i k lv lv' lm hi hk hlm
  · iapply H $$ Hx

theorem big_sepML_lookup_l_app_acc (Φ : K → V → LV → PROP) (m : M V) (lv : LV)
    (l0 l1 : List LV) :
    big_sepML Φ m (l0 ++ lv :: l1) ⊢
      ∃ k v, ⌜get? m k = some v⌝ ∗ Φ k v lv ∗
        ∀ v' lv', Φ k v' lv' -∗ big_sepML Φ (insert m k v') (l0 ++ lv' :: l1) := by
  have h := big_sepML_lookup_l_acc Φ m (l0 ++ lv :: l1) l0.length lv (by simp)
  have hs : ∀ lv' : LV, (l0 ++ lv :: l1).set l0.length lv' = l0 ++ lv' :: l1 := by
    intro lv'; simp
  simp only [hs] at h
  exact h

theorem big_sepML_lookup_m_acc (Φ : K → V → LV → PROP) (m : M V) (l : List LV) (k : K) (v : V) :
    get? m k = some v →
    big_sepML Φ m l ⊢
      ∃ i lv, ⌜l[i]? = some lv⌝ ∗ Φ k v lv ∗
        ∀ v' lv', Φ k v' lv' -∗ big_sepML Φ (insert m k v') (l.set i lv') := by
  intro hm
  unfold big_sepML
  iintro ⟨%lm, %hlm, H⟩
  ihave %hx := (big_sepM2_lookup_l_some Φ m lm k v hm) $$ H
  obtain ⟨xm, hxm⟩ := hx
  icases (bigSepM2_insert_acc hm hxm) $$ H with ⟨Hx, H⟩
  obtain ⟨i, hi⟩ := map_to_list_some_list l k xm lm hxm hlm
  iexists i, xm
  isplitr
  · ipureintro; exact hi
  isplitl [Hx]
  · iexact Hx
  iintro %v' %lv' Hx
  iexists (insert lm k lv')
  isplitr
  · ipureintro; exact map_to_list_insert_overwrite l i k xm lv' lm hi hxm hlm
  · iapply H $$ Hx

theorem big_sepML_mono (Φ Ψ : K → V → LV → PROP) (m : M V) (l : List LV) :
    big_sepML Φ m l ⊢ ⌜∀ k v lv, Φ k v lv ⊢ Ψ k v lv⌝ -∗ big_sepML Ψ m l := by
  iintro H %h
  iapply (big_sepML_proper h (List.Perm.refl l)) $$ H

theorem big_sepML_lookup_l_Some (Φ : K → V → LV → PROP) (m : M V) (l : List LV) (i : Nat)
    (lv : LV) :
    l[i]? = some lv →
    big_sepML Φ m l ⊢ ⌜∃ k v, get? m k = some v⌝ := by
  intro hl
  iintro H
  icases (big_sepML_lookup_l_acc Φ m l i lv hl) $$ H with ⟨%k, %v, %h, _⟩
  ipureintro; exact ⟨k, v, h⟩

theorem big_sepML_lookup_m_Some (Φ : K → V → LV → PROP) (m : M V) (l : List LV) (k : K) (v : V) :
    get? m k = some v →
    big_sepML Φ m l ⊢ ⌜∃ (i : Nat) (lv : LV), l[i]? = some lv⌝ := by
  intro hm
  iintro H
  icases (big_sepML_lookup_m_acc Φ m l k v hm) $$ H with ⟨%i, %lv, %h, _⟩
  ipureintro; exact ⟨i, lv, h⟩

theorem big_sepML_empty_m (Φ : K → V → LV → PROP) (m : M V) :
    big_sepML Φ m [] ⊢ ⌜m = ∅⌝ := by
  unfold big_sepML
  iintro ⟨%lm, %hlm, H⟩
  have hlm' : lm = ∅ := by
    apply eq_empty_iff.mpr
    intro k
    cases h : get? lm k with
    | none => rfl
    | some lv =>
      have : lv ∈ (FiniteMap.toList lm).map Prod.snd :=
        List.mem_map.mpr ⟨(k, lv), toList_get.mpr h, rfl⟩
      exact absurd (hlm.symm.subset this) List.not_mem_nil
  subst hlm'
  iapply (bigSepM2_empty_left m Φ) $$ H

theorem big_sepML_empty_l (Φ : K → V → LV → PROP) (l : List LV) :
    big_sepML Φ (∅ : M V) l ⊢ ⌜l = []⌝ := by
  unfold big_sepML
  iintro ⟨%lm, %hlm, H⟩
  ihave %he := (bigSepM2_empty_right lm Φ) $$ H
  subst he
  ipureintro
  rw [show FiniteMap.toList (∅ : M LV) = [] from LawfulFiniteMap.toList_empty] at hlm
  exact List.perm_nil.mp hlm

theorem big_sepML_sep (Φ Ψ : K → V → LV → PROP) (m : M V) (l : List LV) :
    big_sepML (fun k v lv => iprop(Φ k v lv ∗ Ψ k v lv)) m l ⊢
      big_sepML Φ m l ∗ big_sepML Ψ m l := by
  unfold big_sepML
  iintro ⟨%lm, %hlm, H⟩
  icases bigSepM2_sep_eqv.1 $$ H with ⟨H1, H2⟩
  isplitl [H1]
  · iexists lm
    isplitr
    · ipureintro; exact hlm
    · iexact H1
  · iexists lm
    isplitr
    · ipureintro; exact hlm
    · iexact H2

theorem big_sepML_sepM (Φ : K → V → LV → PROP) (P : K → V → PROP) (m : M V) (l : List LV) :
    big_sepML (fun k v lv => iprop(Φ k v lv ∗ P k v)) m l ⊣⊢
      big_sepML Φ m l ∗ [∗map] k ↦ v ∈ m, P k v := by
  unfold big_sepML
  constructor
  · iintro ⟨%lm, %hlm, H⟩
    icases bigSepM2_sep_eqv.1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists lm
      isplitr
      · ipureintro; exact hlm
      · iexact H1
    · ihave H2 := (big_sepM2_sepM_1 (fun k v (_ : LV) => P k v) m lm) $$ H2
      iapply (bigSepM_mono (Ψ := fun k v => P k v)
        fun _ => exists_elim fun _ => sep_elim_right) $$ H2
  · iintro ⟨⟨%lm, %hlm, H⟩, Hm⟩
    ihave %hdom := (bigSepM2_dom _ m lm) $$ H
    ihave Hm := (big_sepM_sepM2_merge P (fun _ _ => (emp : PROP)) m lm hdom) $$ [$Hm]
    · iapply bigSepM_emp.2
      iempintro
    iexists lm
    isplitr
    · ipureintro; exact hlm
    · ihave H := bigSepM2_sep_eqv.2 $$ [$H $Hm]
      iapply (bigSepM2_mono fun _ _ => sep_mono_right sep_emp.1) $$ H

theorem big_sepML_sepM_ex (Φ : K → V → LV → PROP) (m : M V) (l : List LV) :
    big_sepML Φ m l ⊢ [∗map] k ↦ v ∈ m, ∃ lv, ⌜lv ∈ l⌝ ∗ Φ k v lv := by
  unfold big_sepML
  iintro ⟨%lm, %hlm, H⟩
  ihave H := (big_sepM2_sepM_1 Φ m lm) $$ H
  iapply (bigSepM_mono fun {k v} _ => ?_) $$ H
  iintro ⟨%lv, %hlv, H⟩
  iexists lv
  iframe
  ipureintro
  exact hlm.symm.subset (List.mem_map.mpr ⟨(k, lv), toList_get.mpr hlv, rfl⟩)

theorem big_sepML_sepL_split (Φ : K → V → LV → PROP) (P : LV → PROP) (m : M V) (l : List LV) :
    big_sepML (fun k v lv => iprop(Φ k v lv ∗ P lv)) m l ⊢
      big_sepML Φ m l ∗ [∗list] lv ∈ l, P lv := by
  unfold big_sepML
  iintro ⟨%lm, %hlm, H⟩
  icases bigSepM2_sep_eqv.1 $$ H with ⟨H1, H2⟩
  isplitl [H1]
  · iexists lm
    isplitr
    · ipureintro; exact hlm
    · iexact H1
  · ihave H2 := (big_sepM2_sepM_2 (fun _ (_ : V) lv => P lv) m lm) $$ H2
    ihave H2 := (bigSepM_mono (Ψ := fun _ lv => P lv)
      fun _ => exists_elim fun _ => sep_elim_right) $$ H2
    iapply (bigSepM_snd_perm P lm l hlm).1 $$ H2

theorem big_sepML_sepL_combine (Φ : K → V → LV → PROP) (P : LV → PROP) (m : M V) (l : List LV) :
    big_sepML Φ m l ∗ ([∗list] lv ∈ l, P lv) ⊢
      big_sepML (fun k v lv => iprop(Φ k v lv ∗ P lv)) m l := by
  unfold big_sepML
  iintro ⟨⟨%lm, %hlm, H⟩, Hl⟩
  ihave Hl := (bigSepM_snd_perm P lm l hlm).2 $$ Hl
  ihave %hdom := (bigSepM2_dom _ m lm) $$ H
  ihave Hl := (big_sepM_sepM2_merge (fun _ _ => (emp : PROP)) (fun _ lv => P lv) m lm hdom) $$ [$Hl]
  · iapply bigSepM_emp.2
    iempintro
  iexists lm
  isplitr
  · ipureintro; exact hlm
  · ihave H := bigSepM2_sep_eqv.2 $$ [$H $Hl]
    iapply (bigSepM2_mono fun _ _ => sep_mono_right emp_sep.1) $$ H

theorem big_sepML_sepL (Φ : K → V → LV → PROP) (P : LV → PROP) (m : M V) (l : List LV) :
    big_sepML (fun k v lv => iprop(Φ k v lv ∗ P lv)) m l ⊣⊢
      big_sepML Φ m l ∗ [∗list] lv ∈ l, P lv :=
  ⟨big_sepML_sepL_split Φ P m l, big_sepML_sepL_combine Φ P m l⟩

theorem big_sepML_sepL_exists (Φ : K → V → LV → PROP) (m : M V) (l : List LV) :
    big_sepML Φ m l ⊢ [∗list] lv ∈ l, ∃ k v, ⌜get? m k = some v⌝ ∗ Φ k v lv := by
  unfold big_sepML
  iintro ⟨%lm, %hlm, H⟩
  ihave H := (big_sepM2_sepM_2 Φ m lm) $$ H
  ihave H := (bigSepM_mono (Ψ := fun _ lv => iprop(∃ k v, ⌜get? m k = some v⌝ ∗ Φ k v lv))
    fun {k lv} _ => ?_) $$ H
  · iintro ⟨%v, %hv, H⟩
    iexists k, v
    iframe
    ipureintro; exact hv
  iapply (bigSepM_snd_perm _ lm l hlm).1 $$ H

instance big_sepML_persistent (Φ : K → V → LV → PROP) [∀ k v lv, Persistent (Φ k v lv)]
    (m : M V) (l : List LV) : Persistent (big_sepML Φ m l) := by
  unfold big_sepML
  infer_instance

instance big_sepML_absorbing (Φ : K → V → LV → PROP) [∀ k v lv, Absorbing (Φ k v lv)]
    (m : M V) (l : List LV) : Absorbing (big_sepML Φ m l) := by
  unfold big_sepML
  infer_instance

/-- The pure core of `big_sepML_nodup`: distinct keys of `lm` carry values
with distinct images under `f`. -/
private theorem big_sepM2_distinct {T : Type _} (f : LV → T) (Φ : K → V → LV → PROP) (m : M V)
    (lm : M LV) :
    ([∗map] k ↦ v;lv ∈ m;lm, Φ k v lv) ∗
      (∀ k1 k2 v1 v2 lv1 lv2, ⌜f lv1 = f lv2⌝ -∗ Φ k1 v1 lv1 -∗ Φ k2 v2 lv2 -∗ ⌜k1 = k2⌝) ⊢
    ⌜∀ k1 k2 lv1 lv2, get? lm k1 = some lv1 → get? lm k2 = some lv2 → k1 ≠ k2 →
      f lv1 ≠ f lv2⌝ := by
  refine .trans ?_ pure_forall.2; refine forall_intro fun k1 => ?_
  refine .trans ?_ pure_forall.2; refine forall_intro fun k2 => ?_
  refine .trans ?_ pure_forall.2; refine forall_intro fun lv1 => ?_
  refine .trans ?_ pure_forall.2; refine forall_intro fun lv2 => ?_
  by_cases hc : get? lm k1 = some lv1 ∧ get? lm k2 = some lv2 ∧ k1 ≠ k2 ∧ f lv1 = f lv2
  · obtain ⟨h1, h2, hne, hf⟩ := hc
    iintro ⟨H, Heq⟩
    ihave %hm1 := (big_sepM2_lookup_r_some Φ m lm k1 lv1 h1) $$ H
    obtain ⟨v1, hv1⟩ := hm1
    icases (bigSepM2_delete hv1 h1).1 $$ H with ⟨Hi, H⟩
    have h2' : get? (delete lm k1) k2 = some lv2 := by rw [get?_delete_ne hne]; exact h2
    ihave %hm2 := (big_sepM2_lookup_r_some Φ _ _ k2 lv2 h2') $$ H
    obtain ⟨v2, hv2⟩ := hm2
    icases (bigSepM2_delete hv2 h2').1 $$ H with ⟨Hj, _⟩
    ihave %hk := Heq $$ %k1 %k2 %v1 %v2 %lv1 %lv2 %hf Hi Hj
    exact absurd hk hne
  · iintro _
    ipureintro
    intro h1 h2 hne hf
    exact absurd ⟨h1, h2, hne, hf⟩ hc

theorem big_sepML_nodup {T : Type _} (f : LV → T) (Φ : K → V → LV → PROP) (m : M V)
    (l : List LV) :
    big_sepML Φ m l ⊢
      (∀ k1 k2 v1 v2 lv1 lv2, ⌜f lv1 = f lv2⌝ -∗ Φ k1 v1 lv1 -∗ Φ k2 v2 lv2 -∗ ⌜k1 = k2⌝) -∗
      ⌜(l.map f).Nodup⌝ := by
  unfold big_sepML
  iintro ⟨%lm, %hlm, H⟩ Heq
  ihave %hd := (big_sepM2_distinct f Φ m lm) $$ [$H $Heq]
  ipureintro
  rw [(hlm.map f).nodup_iff, List.map_map]
  have hk : ((FiniteMap.toList lm).map Prod.fst).Nodup := toList_noDupKeys
  unfold List.Nodup at hk ⊢
  rw [List.pairwise_map] at hk ⊢
  refine hk.imp_of_mem fun {a b} ha hb hab => ?_
  obtain ⟨k1, lv1⟩ := a
  obtain ⟨k2, lv2⟩ := b
  exact hd k1 k2 lv1 lv2 (toList_get.mp ha) (toList_get.mp hb) hab

end maplist

section maplist2

variable {V W LV : Type u}

theorem big_sepML_map_val_exists_helper (Φ : K → V → LV → PROP) (mv : M V) (l : List LV)
    (R : K → V → W → Prop) :
    big_sepML Φ mv l ⊢
      □ (∀ k v lv, ⌜get? mv k = some v⌝ -∗ Φ k v lv -∗ ⌜∃ w, R k v w⌝) -∗
      ∃ mw : M W, ⌜dom mw = dom mv⌝ ∗
        big_sepML (fun k w lv => iprop(∃ v, ⌜R k v w⌝ ∗ Φ k v lv)) mw l := by
  induction l generalizing mv with
  | nil =>
    iintro Hml #_
    ihave %he := (big_sepML_empty_m Φ mv) $$ Hml
    subst he
    iexists (∅ : M W)
    isplitr
    · ipureintro; funext k; simp [dom, get?_empty]
    · iapply big_sepML_empty
  | cons lv l ih =>
    iintro Hml #HR
    icases (big_sepML_delete_cons Φ mv l lv) $$ Hml with ⟨%k, %v, %hkv, Hk, Hml⟩
    ihave %hw := HR $$ %k %v %lv %hkv Hk
    obtain ⟨w, hw⟩ := hw
    icases (ih (delete mv k)) $$ Hml [#] with ⟨%mw, %hdom, Hi⟩
    · iintro !> %k' %v' %lv' %h H
      iapply HR $$ %k' %v' %lv' %((get?_delete_some_iff.mp h).2) H
    have hmw : get? mw k = none := by
      have := map_dom_eq_iff.mp hdom k
      rw [get?_delete_eq rfl] at this
      cases h : get? mw k <;> simp_all
    iexists (insert mw k w)
    isplitr
    · ipureintro
      apply map_dom_eq_iff.mpr
      intro k'
      have := map_dom_eq_iff.mp hdom k'
      by_cases hk : k = k'
      · subst hk; simp [get?_insert_eq rfl, hkv]
      · rw [get?_insert_ne hk]; rw [get?_delete_ne hk] at this; exact this
    · iapply (big_sepML_insert _ mw l k w lv hmw)
      isplitl [Hk]
      · iexists v
        iframe
        ipureintro; exact hw
      · iexact Hi

theorem big_sepML_map_val_exists (Φ : K → V → LV → PROP) (mv : M V) (l : List LV)
    (R : K → V → W → Prop) :
    big_sepML Φ mv l ⊢
      □ (∀ k v lv, ⌜get? mv k = some v⌝ -∗ Φ k v lv -∗ ⌜∃ w, R k v w⌝) -∗
      ∃ mw : M W, big_sepML (fun k w lv => iprop(∃ v, ⌜R k v w⌝ ∗ Φ k v lv)) mw l := by
  iintro Hml #HR
  icases (big_sepML_map_val_exists_helper Φ mv l R) $$ Hml HR with ⟨%mw, _, H⟩
  iexists mw
  iexact H

theorem big_sepML_exists (Φw : K → V → LV → W → PROP) (m : M V) (l : List LV) :
    big_sepML (fun k v lv => iprop(∃ w, Φw k v lv w)) m l ⊢
      ∃ lw : List (LV × W), ⌜l = lw.map Prod.fst⌝ ∗
        big_sepML (fun k v lv => Φw k v lv.1 lv.2) m lw := by
  induction l generalizing m with
  | nil =>
    iintro Hml
    ihave %he := (big_sepML_empty_m _ m) $$ Hml
    subst he
    iexists ([] : List (LV × W))
    isplitr
    · ipureintro; rfl
    · iapply big_sepML_empty
  | cons a l ih =>
    iintro Hml
    icases (big_sepML_delete_cons _ m l a) $$ Hml with ⟨%k, %v, %hkv, ⟨%w, Hk⟩, Hml⟩
    icases (ih (delete m k)) $$ Hml with ⟨%lw, %hlw, Hi⟩
    iexists ((a, w) :: lw)
    isplitr
    · ipureintro; simp [hlw]
    · have e := big_sepML_insert (fun k v (lv : LV × W) => Φw k v lv.1 lv.2) (delete m k) lw k v
        (a, w) (get?_delete_eq rfl)
      rw [insert_delete_cancel hkv] at e
      iapply e
      iframe

theorem big_sepML_fmap (Φ : K → V → LV → PROP) (f : W → V) (mw : M W) (l : List LV) :
    big_sepML Φ (map f mw) l ⊣⊢ big_sepML (fun k w lv => Φ k (f w) lv) mw l := by
  unfold big_sepML
  have h : ∀ lm : M LV, ([∗map] k ↦ v;lvm ∈ map f mw;lm, Φ k v lvm) =
      ([∗map] k ↦ w;lvm ∈ mw;lm, Φ k (f w) lvm) :=
    fun lm => (bigSepM2_map_left f Φ mw lm).to_eq
  simp only [h]
  exact .rfl

end maplist2

theorem big_sepML_change_m {V0 V1 LV : Type u} (m0 : M V0) (m1 : M V1) (l : List LV)
    (Φ : K → LV → PROP) :
    dom m0 = dom m1 →
    big_sepML (fun k _ lv => Φ k lv) m0 l ⊢ big_sepML (fun k _ lv => Φ k lv) m1 l := by
  intro hdom
  unfold big_sepML
  iintro ⟨%lm, %hlm, H⟩
  ihave %hd := (bigSepM2_dom _ m0 lm) $$ H
  ihave H := (big_sepM2_sepM_2 (fun k (_ : V0) lv => Φ k lv) m0 lm) $$ H
  ihave H := (bigSepM_mono (Ψ := fun k lv => Φ k lv)
    fun _ => exists_elim fun _ => sep_elim_right) $$ H
  iexists lm
  isplitr
  · ipureintro; exact hlm
  · ihave H := (big_sepM_sepM2_merge (fun _ _ => (emp : PROP)) (fun k lv => Φ k lv) m1 lm
      (hdom.symm.trans hd)) $$ [$H]
    · iapply bigSepM_emp.2
      iempintro
    iapply (bigSepM2_mono fun _ _ => emp_sep.1) $$ H

theorem big_sepL_impl {A : Type _} (f g : Nat → A → PROP) (l : List A) :
    (∀ i x, f i x ⊢ g i x) →
    ([∗list] i ↦ x ∈ l, f i x) ⊢ [∗list] i ↦ x ∈ l, g i x :=
  fun h => bigSepL_mono fun _ => h _ _

end bi

end Perennial
