/-
Extra lemmas about big separating conjunctions over lists.

Only lemmas that iris-lean's `Iris.BI.BigOp.BigSepList` lacks are included.
* Statements are entailments `P ⊢ Q` rather than `⊢ P -∗ Q` (or a meta-level hypothesis `P -∗ Q`).
* `big_sepL2_const_sepL_l/r` are aliases of iris-lean's `bigSepL2_const_sepL_left/right`.
  `big_sepL2_sep_sepL_l/r` are re-proved here because iris-lean's versions need `BIAffine`.
* `big_sepL2_fupd` is iris-lean's `BigSepL2.bigSepL2_fupd` and is not repeated.
* `big_sepL2_mono_with_inv` and `big_sepL2_mono_with_fupd_inv` do not need `BIAffine`.
-/
module

public import Iris.BI
public import Iris.BI.BigOp
public import Iris.BI.Updates
public import Iris.ProofMode

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.BI.BigSepL Iris.BI.BigSepL2

section list
variable {PROP : Type _} [BI PROP]

theorem wlog_assume_pure (φ : Prop) {P Q : PROP} (hP : P ⊢ ⌜φ⌝) (hQ : Q ⊢ ⌜φ⌝)
    (hPQ : φ → P ⊣⊢ Q) : P ⊣⊢ Q :=
  ⟨pure_elim φ hP fun h => (hPQ h).1, pure_elim φ hQ fun h => (hPQ h).2⟩

theorem big_sepL_replicate_impl (Φ Ψ : PROP) (n : Nat) :
    ([∗list] P ∈ List.replicate n Φ, P) ⊢ □ (Φ -∗ Ψ) -∗ [∗list] P ∈ List.replicate n Ψ, P := by
  induction n with
  | zero => exact wand_intro (sep_elim_left (P := emp))
  | succ n ih =>
    rw [List.replicate_succ, List.replicate_succ]
    iintro H #Hi
    icases bigSepL_cons.1 $$ H with ⟨HΦ, H⟩
    iapply bigSepL_cons.2
    isplitl [HΦ]
    · iapply Hi $$ HΦ
    · iapply ih $$ H Hi

theorem big_sepL_take [BIAffine PROP] {A : Type _} (Φ : Nat → A → PROP) (m : List A) (n : Nat) :
    ([∗list] k ↦ x ∈ m, Φ k x) ⊢ [∗list] k ↦ x ∈ m.take n, Φ k x :=
  (bigSepL_take_drop (n := n)).1.trans sep_elim_left

theorem big_sepL_drop [BIAffine PROP] {A : Type _} (Φ : Nat → A → PROP) (m : List A) (n : Nat) :
    ([∗list] k ↦ x ∈ m, Φ k x) ⊢ [∗list] k ↦ x ∈ m.drop n, Φ (n + k) x :=
  (bigSepL_take_drop (n := n)).1.trans sep_elim_right

private theorem big_sepL_mono_with_inv_core {A : Type _} (P : PROP) :
    ∀ (Φ Ψ : Nat → A → PROP) (m : List A),
    (∀ k x, m[k]? = some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) →
    P ∗ ([∗list] k ↦ x ∈ m, Φ k x) ⊢ P ∗ [∗list] k ↦ x ∈ m, Ψ k x
  | _, _, [], _ => .rfl
  | Φ, Ψ, a :: m, h =>
    sep_assoc.2.trans <| (sep_mono_left (h 0 a rfl)).trans <| sep_assoc.1.trans <|
      sep_left_comm.1.trans <|
      (sep_mono_right (big_sepL_mono_with_inv_core P (fun k => Φ (k + 1)) (fun k => Ψ (k + 1)) m
        fun k x hk => h (k + 1) x hk)).trans sep_left_comm.1

theorem big_sepL_mono_with_inv' {A : Type _} (P : PROP) (Φ Ψ : Nat → A → PROP) (m : List A)
    (n : Nat) (h : ∀ k x, m[k]? = some x → P ∗ Φ (k + n) x ⊢ P ∗ Ψ (k + n) x) :
    P ∗ ([∗list] k ↦ x ∈ m, Φ (k + n) x) ⊢ P ∗ [∗list] k ↦ x ∈ m, Ψ (k + n) x :=
  big_sepL_mono_with_inv_core P (fun k => Φ (k + n)) (fun k => Ψ (k + n)) m h

theorem big_sepL_mono_with_inv {A : Type _} (P : PROP) (Φ Ψ : Nat → A → PROP) (m : List A)
    (h : ∀ k x, m[k]? = some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) :
    P ⊢ ([∗list] k ↦ x ∈ m, Φ k x) -∗ P ∗ [∗list] k ↦ x ∈ m, Ψ k x :=
  wand_intro (big_sepL_mono_with_inv_core P Φ Ψ m h)

section list2
variable {A B : Type _}

theorem big_sepL2_const_sepL_l (Φ : Nat → A → PROP) (l1 : List A) (l2 : List B) :
    ([∗list] k ↦ y1;_y2 ∈ l1;l2, Φ k y1) ⊣⊢
      ⌜l1.length = l2.length⌝ ∧ [∗list] k ↦ y1 ∈ l1, Φ k y1 :=
  bigSepL2_const_sepL_left

theorem big_sepL2_const_sepL_r (Φ : Nat → B → PROP) (l1 : List A) (l2 : List B) :
    ([∗list] k ↦ _y1;y2 ∈ l1;l2, Φ k y2) ⊣⊢
      ⌜l1.length = l2.length⌝ ∧ [∗list] k ↦ y2 ∈ l2, Φ k y2 :=
  bigSepL2_const_sepL_right

theorem big_sepL2_sep_sepL_l (Φ : Nat → A → PROP) (Ψ : Nat → A → B → PROP)
    (l1 : List A) (l2 : List B) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 ∗ Ψ k y1 y2) ⊣⊢
      ([∗list] k ↦ y1 ∈ l1, Φ k y1) ∗ [∗list] k ↦ y1;y2 ∈ l1;l2, Ψ k y1 y2 :=
  bigSepL2_sep_eqv.trans <| (sep_congr_left bigSepL2_const_sepL_left).trans
    ⟨sep_mono_left and_elim_r,
     pure_elim (l1.length = l2.length) ((sep_mono_right bigSepL2_length).trans sep_elim_right)
       fun h => sep_mono_left (and_intro (pure_intro h) .rfl)⟩

theorem big_sepL2_sep_sepL_r (Φ : Nat → A → B → PROP) (Ψ : Nat → B → PROP)
    (l1 : List A) (l2 : List B) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2 ∗ Ψ k y2) ⊣⊢
      ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ∗ [∗list] k ↦ y2 ∈ l2, Ψ k y2 :=
  bigSepL2_sep_eqv.trans <| (sep_congr_right bigSepL2_const_sepL_right).trans
    ⟨sep_mono_right and_elim_r,
     pure_elim (l1.length = l2.length) ((sep_mono_left bigSepL2_length).trans sep_elim_left)
       fun h => sep_mono_right (and_intro (pure_intro h) .rfl)⟩

theorem big_sepL2_elim_big_sepL [BIAffine PROP] {C : Type _} (P : Nat → C → PROP)
    (Φ : Nat → A → B → PROP) (l1 : List A) (l2 : List B) (l : List C)
    (hlen : l.length = l1.length) :
    □ (∀ k x y z, ⌜l1[k]? = some x⌝ -∗ ⌜l2[k]? = some y⌝ -∗ ⌜l[k]? = some z⌝ -∗
        Φ k x y -∗ P k z) ⊢
      ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) -∗ [∗list] k ↦ z ∈ l, P k z := by
  induction l generalizing l1 l2 Φ P with
  | nil => iintro - -; iempintro
  | cons c l ih =>
    cases l1 with
    | nil => simp at hlen
    | cons x l1 =>
      cases l2 with
      | nil => simp only [bigSepL2]; iintro - H; iexfalso; iexact H
      | cons y l2 =>
        iintro #Hi ⟨H0, H⟩
        isplitl [H0]
        · iapply Hi $$ %0 %x %y %c %rfl %rfl %rfl H0
        · iapply ih (fun k => P (k + 1)) (fun k => Φ (k + 1)) l1 l2 (by simpa using hlen) $$ [] H
          iintro !> %k %x' %y' %z %h1 %h2 %h3 HΦ
          iapply Hi $$ %(k + 1) %x' %y' %z %h1 %h2 %h3 HΦ

theorem big_sepL2_elim_big_sepL_aux [BIAffine PROP] {C : Type _} (P : Nat → C → PROP)
    (Φ : Nat → A → B → PROP) (l1 : List A) (l2 : List B) (l : List C) (n : Nat)
    (hlen : l.length = l1.length) :
    □ (∀ k x y z, ⌜l1[k]? = some x⌝ -∗ ⌜l2[k]? = some y⌝ -∗ ⌜l[k]? = some z⌝ -∗
        Φ (k + n) x y -∗ P (k + n) z) ⊢
      ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ (k + n) y1 y2) -∗ [∗list] k ↦ z ∈ l, P (k + n) z :=
  big_sepL2_elim_big_sepL (fun k => P (k + n)) (fun k => Φ (k + n)) l1 l2 l hlen

/-- An equivalence, given a separate length assumption. -/
theorem big_sepL2_to_sepL_1' (Φ : Nat → A → B → PROP) (l1 : List A) (l2 : List B)
    (hlen : l1.length = l2.length) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
      [∗list] k ↦ y1 ∈ l1, ∃ y2, ⌜l2[k]? = some y2⌝ ∧ Φ k y1 y2 := by
  induction l1 generalizing l2 Φ with
  | nil =>
    cases l2 with
    | nil => exact .rfl
    | cons => simp at hlen
  | cons x l1 ih =>
    cases l2 with
    | nil => simp at hlen
    | cons y l2 =>
      refine sep_congr ⟨exists_intro_trans y (and_intro (pure_intro rfl) .rfl),
        exists_elim fun y2 => pure_elim_left fun h => ?_⟩
        ((ih (fun k => Φ (k + 1)) l2 (by simpa using hlen)).trans
          (BiEntails.of_eq (bigSepL_eq_of_forall_eq (by simp))))
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; exact .rfl

theorem big_sepL2_to_sepL_1 (Φ : Nat → A → B → PROP) (l1 : List A) (l2 : List B) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
      [∗list] k ↦ y1 ∈ l1, ∃ y2, ⌜l2[k]? = some y2⌝ ∧ Φ k y1 y2 :=
  pure_elim _ bigSepL2_length fun h => (big_sepL2_to_sepL_1' Φ l1 l2 h).1

theorem big_sepL2_to_sepL_2' (Φ : Nat → A → B → PROP) (l1 : List A) (l2 : List B)
    (hlen : l1.length = l2.length) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
      [∗list] k ↦ y2 ∈ l2, ∃ y1, ⌜l1[k]? = some y1⌝ ∧ Φ k y1 y2 :=
  bigSepL2_flip.symm.trans (big_sepL2_to_sepL_1' (fun k y x => Φ k x y) l2 l1 hlen.symm)

theorem big_sepL2_to_sepL_2 (Φ : Nat → A → B → PROP) (l1 : List A) (l2 : List B) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
      [∗list] k ↦ y2 ∈ l2, ∃ y1, ⌜l1[k]? = some y1⌝ ∧ Φ k y1 y2 :=
  bigSepL2_flip.2.trans (big_sepL2_to_sepL_1 (fun k y x => Φ k x y) l2 l1)

theorem big_sepL2_lookup_1_some (Φ : Nat → A → B → PROP) (l1 : List A) (l2 : List B)
    (i : Nat) (x1 : A) (h : l1[i]? = some x1) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ ⌜∃ x2, l2[i]? = some x2⌝ :=
  bigSepL2_length.trans <| pure_mono fun hlen => by
    have := (List.getElem?_eq_some_iff.mp h).1
    exact ⟨l2[i]'(by omega), List.getElem?_eq_getElem _⟩

theorem big_sepL2_lookup_2_some (Φ : Nat → A → B → PROP) (l1 : List A) (l2 : List B)
    (i : Nat) (x2 : B) (h : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ ⌜∃ x1, l1[i]? = some x1⌝ :=
  bigSepL2_length.trans <| pure_mono fun hlen => by
    have := (List.getElem?_eq_some_iff.mp h).1
    exact ⟨l1[i]'(by omega), List.getElem?_eq_getElem _⟩

theorem big_sepL2_lookup_1_none (Φ : Nat → A → B → PROP) (l1 : List A) (l2 : List B)
    (i : Nat) (h : l1[i]? = none) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ ⌜l2[i]? = none⌝ :=
  bigSepL2_length.trans <| pure_mono fun hlen => by
    have := List.getElem?_eq_none_iff.mp h
    exact List.getElem?_eq_none_iff.mpr (by omega)

theorem big_sepL2_lookup_2_none (Φ : Nat → A → B → PROP) (l1 : List A) (l2 : List B)
    (i : Nat) (h : l2[i]? = none) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ ⌜l1[i]? = none⌝ :=
  bigSepL2_length.trans <| pure_mono fun hlen => by
    have := List.getElem?_eq_none_iff.mp h
    exact List.getElem?_eq_none_iff.mpr (by omega)

theorem big_sepL_exists_to_sepL2 (Φ : Nat → A → B → PROP) (l : List A) :
    ([∗list] i ↦ a ∈ l, ∃ x, Φ i a x) ⊢ ∃ xs, [∗list] i ↦ a;x ∈ l;xs, Φ i a x := by
  induction l generalizing Φ with
  | nil => exact exists_intro_trans [] .rfl
  | cons a l ih =>
    iintro ⟨⟨%x, H0⟩, H⟩
    icases ih (fun k => Φ (k + 1)) $$ H with ⟨%xs, H⟩
    iexists (x :: xs)
    iapply bigSepL2_cons.2
    isplitl [H0]
    · iexact H0
    · iexact H

theorem big_sepL_exists_list (Φ : Nat → A → B → PROP) (l : List A) :
    ([∗list] i ↦ a ∈ l, ∃ x, Φ i a x) ⊢
      ∃ xs : List B, ⌜xs.length = l.length⌝ ∧
        [∗list] i ↦ a ∈ l, ∃ x, ⌜xs[i]? = some x⌝ ∧ Φ i a x :=
  (big_sepL_exists_to_sepL2 Φ l).trans <| exists_elim fun xs =>
    exists_intro_trans xs <| pure_elim _ bigSepL2_length fun h =>
      and_intro (pure_intro h.symm) (big_sepL2_to_sepL_1' Φ l xs h).1

theorem big_sepL2_app_equiv (Φ : Nat → A → B → PROP) (l1 l2 : List A) (l1' l2' : List B)
    (hlen : l1.length = l1'.length) :
    ([∗list] k ↦ y1;y2 ∈ l1;l1', Φ k y1 y2) ∗
      ([∗list] k ↦ y1;y2 ∈ l2;l2', Φ (l1.length + k) y1 y2) ⊣⊢
      [∗list] k ↦ y1;y2 ∈ l1 ++ l2;l1' ++ l2', Φ k y1 y2 :=
  (bigSepL2_app_same_length (Or.inl hlen)).symm

/-- A general theorem, but `Φc` suggests a weaker crash condition for each element. -/
theorem big_sepL2_lookup_acc_and (Φ Φc : Nat → A → B → PROP) (l1 : List A) (l2 : List B)
    (i : Nat) (x1 : A) (x2 : B)
    (himpl : ∀ k y1 y2, l1[k]? = some y1 → l2[k]? = some y2 → Φ k y1 y2 ⊢ Φc k y1 y2)
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    bigSepL2 Φ l1 l2 ⊢
      Φ i x1 x2 ∗ ((Φ i x1 x2 -∗ bigSepL2 Φ l1 l2) ∧ (Φc i x1 x2 -∗ bigSepL2 Φc l1 l2)) :=
  (bigSepL2_delete_cond h1 h2).1.trans <| sep_mono_right <| and_intro
    (wand_intro (sep_comm.1.trans (bigSepL2_delete_cond h1 h2).2))
    (wand_intro <| sep_comm.1.trans <| (sep_mono_right (bigSepL2_mono fun {k _ _} hk1 hk2 => by
        split
        · exact .rfl
        · exact himpl _ _ _ hk1 hk2)).trans (bigSepL2_delete_cond h1 h2).2)

theorem big_sepL2_prefix [BIAffine PROP] (Φ : A → B → PROP) (l1 l1' : List A)
    (l2 l2' : List B) (hpre1 : l1' <+: l1) (hpre2 : l2' <+: l2)
    (hlen : l1'.length = l2'.length) :
    ([∗list] y1;y2 ∈ l1;l2, Φ y1 y2) ⊢ [∗list] y1;y2 ∈ l1';l2', Φ y1 y2 := by
  obtain ⟨r1, rfl⟩ := hpre1
  obtain ⟨r2, rfl⟩ := hpre2
  exact (bigSepL2_append (Or.inl hlen)).1.trans sep_elim_left

theorem big_sepL2_suffix [BIAffine PROP] (Φ : A → B → PROP) (l1 l1' : List A)
    (l2 l2' : List B) (hsuf1 : l1' <:+ l1) (hsuf2 : l2' <:+ l2)
    (hlen : l1'.length = l2'.length) :
    ([∗list] y1;y2 ∈ l1;l2, Φ y1 y2) ⊢ [∗list] y1;y2 ∈ l1';l2', Φ y1 y2 := by
  obtain ⟨r1, rfl⟩ := hsuf1
  obtain ⟨r2, rfl⟩ := hsuf2
  exact pure_elim _ bigSepL2_length fun h =>
    (bigSepL2_append (Or.inl (by simp at h; omega))).1.trans sep_elim_right

end list2

section fupd
variable [BIFUpdate PROP]

private theorem big_sepL_mono_with_fupd_inv_core {A : Type _} (E : CoPset) (P : PROP) :
    ∀ (Φ Ψ : Nat → A → PROP) (m : List A),
    (∀ k x, m[k]? = some x → P ∗ Φ k x ⊢ |={E}=> P ∗ Ψ k x) →
    P ∗ ([∗list] k ↦ x ∈ m, Φ k x) ⊢ |={E}=> P ∗ [∗list] k ↦ x ∈ m, Ψ k x
  | _, _, [], _ => fupd_intro
  | Φ, Ψ, a :: m, h =>
    sep_assoc.2.trans <| (sep_mono_left (h 0 a rfl)).trans <| fupd_frame_right.trans <|
      fupd_mono (sep_assoc.1.trans <| sep_left_comm.1.trans <|
        (sep_mono_right (big_sepL_mono_with_fupd_inv_core E P (fun k => Φ (k + 1))
          (fun k => Ψ (k + 1)) m fun k x hk => h (k + 1) x hk)).trans <|
        fupd_frame_left.trans (fupd_mono sep_left_comm.1)) |>.trans fupd_trans

theorem big_sepL_mono_with_fupd_inv' {A : Type _} (E : CoPset) (P : PROP)
    (Φ Ψ : Nat → A → PROP) (m : List A) (n : Nat)
    (h : ∀ k x, m[k]? = some x → P ∗ Φ (k + n) x ⊢ |={E}=> P ∗ Ψ (k + n) x) :
    P ∗ ([∗list] k ↦ x ∈ m, Φ (k + n) x) ⊢ |={E}=> P ∗ [∗list] k ↦ x ∈ m, Ψ (k + n) x :=
  big_sepL_mono_with_fupd_inv_core E P (fun k => Φ (k + n)) (fun k => Ψ (k + n)) m h

theorem big_sepL_mono_with_fupd_inv {A : Type _} (E : CoPset) (P : PROP)
    (Φ Ψ : Nat → A → PROP) (m : List A)
    (h : ∀ k x, m[k]? = some x → P ∗ Φ k x ⊢ |={E}=> P ∗ Ψ k x) :
    P ⊢ ([∗list] k ↦ x ∈ m, Φ k x) -∗ |={E}=> P ∗ [∗list] k ↦ x ∈ m, Ψ k x :=
  wand_intro (big_sepL_mono_with_fupd_inv_core E P Φ Ψ m h)

end fupd

section list2
variable {A B : Type _}

theorem big_sepL2_mono_with_inv (P : PROP) (Φ Ψ : Nat → A → B → PROP) (l1 : List A)
    (l2 : List B)
    (h : ∀ k x y, l1[k]? = some x → l2[k]? = some y → P ∗ Φ k x y ⊢ P ∗ Ψ k x y) :
    P ⊢ ([∗list] k ↦ x;y ∈ l1;l2, Φ k x y) -∗ P ∗ [∗list] k ↦ x;y ∈ l1;l2, Ψ k x y := by
  refine wand_intro ?_
  induction l1 generalizing l2 Φ Ψ with
  | nil => cases l2 with
    | nil => exact .rfl
    | cons => exact sep_mono_right false_elim
  | cons a l1 ih => cases l2 with
    | nil => exact sep_mono_right false_elim
    | cons b l2 =>
      exact sep_assoc.2.trans <| (sep_mono_left (h 0 a b rfl rfl)).trans <| sep_assoc.1.trans <|
        sep_left_comm.1.trans <|
        (sep_mono_right (ih (fun k => Φ (k + 1)) (fun k => Ψ (k + 1)) l2
          fun k x y hk1 hk2 => h (k + 1) x y hk1 hk2)).trans sep_left_comm.1

theorem big_sepL2_mono_with_fupd_inv [BIFUpdate PROP] (E : CoPset) (P : PROP)
    (Φ Ψ : Nat → A → B → PROP) (l1 : List A) (l2 : List B)
    (h : ∀ k x y, l1[k]? = some x → l2[k]? = some y → P ∗ Φ k x y ⊢ |={E}=> P ∗ Ψ k x y) :
    P ⊢ ([∗list] k ↦ x;y ∈ l1;l2, Φ k x y) -∗ |={E}=> P ∗ [∗list] k ↦ x;y ∈ l1;l2, Ψ k x y := by
  refine wand_intro ?_
  induction l1 generalizing l2 Φ Ψ with
  | nil => cases l2 with
    | nil => exact fupd_intro
    | cons => exact (sep_mono_right false_elim).trans fupd_intro
  | cons a l1 ih => cases l2 with
    | nil => exact (sep_mono_right false_elim).trans fupd_intro
    | cons b l2 =>
      exact sep_assoc.2.trans <| (sep_mono_left (h 0 a b rfl rfl)).trans <|
        fupd_frame_right.trans <| (fupd_mono (sep_assoc.1.trans <| sep_left_comm.1.trans <|
          (sep_mono_right (ih (fun k => Φ (k + 1)) (fun k => Ψ (k + 1)) l2
            fun k x y hk1 hk2 => h (k + 1) x y hk1 hk2)).trans <|
          fupd_frame_left.trans (fupd_mono sep_left_comm.1))).trans fupd_trans

end list2

end list

end Perennial
