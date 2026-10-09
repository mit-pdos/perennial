module

public import Perennial.Ghost.Own

@[expose] public section

/-!
The "authoritative
contribution" ghost theory (from Actris) for tracking the contributions `x : A` of clients
to a shared effort.

* `server γ n x`: there are `n` active clients, holding `x : A` in total;
* `client γ x`: a single client holding `x : A`.

The camera is `auth (option (csum (positive * A) (excl unit)))`. With the universal `allG`
camera (see `Perennial/Ghost/All.lean`), the only requirement is that the discrete unital
camera `A` has a code: `[IsCmra (IProp GF) A a]`. Positive numbers
are `Perennial.positive` (code `positiveR`, added to `Ghost/All.lean` for this file).
-/

set_option autoImplicit false

noncomputable section

namespace Perennial
open Iris OFE CMRA BI ProofMode

section contribution
variable {GF : BundledGFunctors} [AllG GF]
variable {A : Type} [UCMRA A] [CMRA.Discrete A] {ea : Syntax.Cmra} [IsCmra (IProp GF) A ea]

/-- The underlying (unital) camera `option (csum (positive * A) (excl unit))`. -/
abbrev ContribT (A : Type) [UCMRA A] : Type := Option (Csum (positive × A) (Excl Unit))

/-- `Some (Cinl (q, x))`. -/
abbrev contribCl (q : positive) (x : A) : ContribT A := some (.inl (q, x))
/-- `Some (Cinr (Excl ()))`. -/
abbrev contribCr : ContribT A := some (.inr (Excl.excl ()))

def server (γ : GName) (n : Nat) (x : A) : IProp GF :=
  if n = 0 then
    iprop(x ≡ UCMRA.unit ∗ own γ (Auth.auth (DFrac.own 1) (contribCr (A := A))) ∗
      own γ (Auth.frag (contribCr (A := A))))
  else own γ (Auth.auth (DFrac.own 1) (contribCl (positive.ofNat n) x))

def client (γ : GName) (x : A) : IProp GF :=
  own γ (Auth.frag (contribCl positive.one x))

/-! ### Concrete facts about the camera -/

omit [CMRA.Discrete A] in
theorem contribCl_op (p q : positive) (x y : A) :
    contribCl p x • contribCl q y = contribCl (p + q) (x • y) := rfl

omit [CMRA.Discrete A] in
theorem contribCl_valid (p : positive) (x : A) : ✓ contribCl p x ↔ ✓ x :=
  ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

omit [CMRA.Discrete A] in
/-- Decomposition of `contribCl p x • z`. -/
theorem contribCl_op_eq (p q : positive) (x y : A) (z : ContribT A)
    (h : contribCl q y = contribCl p x • z) :
    (q = p ∧ y = x ∧ z = none) ∨ ∃ r w, q = p + r ∧ y = x • w ∧ z = contribCl r w := by
  rcases z with _ | (⟨r, w⟩ | b | _)
  · left; cases h; exact ⟨rfl, rfl, rfl⟩
  · right; cases h; exact ⟨r, w, rfl, rfl, rfl⟩
  · cases h
  · cases h

omit [CMRA.Discrete A] in
theorem contribCl_inc (p q : positive) (x y : A) (h : contribCl p x ≼ contribCl q y) :
    (q = p ∧ y = x) ∨ ∃ r, q = p + r ∧ x ≼ y := by
  obtain ⟨z, hz⟩ := h
  rcases contribCl_op_eq p q x y z hz with ⟨h1, h2, _⟩ | ⟨r, w, h1, h2, _⟩
  · exact .inl ⟨h1, h2⟩
  · exact .inr ⟨r, h1, ⟨w, h2⟩⟩

theorem positive_add_ne_self (p r : positive) : p + r ≠ p := by
  intro h; have := congrArg positive.pred h; simp at this; omega

theorem own_valid_pure {B : Type} [CMRA B] [CMRA.Discrete B] {eb : Syntax.Cmra}
    [IsCmra (IProp GF) B eb] (γ : GName) (b : B) : own γ b ⊢ ⌜✓ b⌝ :=
  (own_valid γ b).trans ((internalCmraValid_elim b).trans (pure_mono CMRA.discrete_valid))

theorem own_valid_pure_2 {B : Type} [CMRA B] [CMRA.Discrete B] {eb : Syntax.Cmra}
    [IsCmra (IProp GF) B eb] (γ : GName) (b1 b2 : B) : own γ b1 ⊢ own γ b2 -∗ ⌜✓ (b1 • b2)⌝ :=
  wand_intro ((own_op γ b1 b2).2.trans (own_valid_pure γ _))

/-! ### Lemmas -/

instance server_ne (γ : GName) (n : Nat) : NonExpansive (server (GF := GF) (A := A) γ n) :=
  ⟨fun {_ x y} h => by cases OFE.Discrete.discrete h; exact .rfl⟩

instance client_ne (γ : GName) : NonExpansive (client (GF := GF) (A := A) γ) :=
  ⟨fun {_ x y} h => by cases OFE.Discrete.discrete h; exact .rfl⟩

theorem contribution_init : ⊢ |==> ∃ γ, server (GF := GF) γ 0 (UCMRA.unit : A) := by
  iapply (BIUpdate.mono ?_) $$ []
  rotate_left
  · iapply (own_alloc ((Auth.auth (DFrac.own 1) (contribCr (A := A))) • Auth.frag contribCr)
      (Auth.auth_both_valid_2 trivial (CMRA.inc_refl _)))
  iintro ⟨%γ, H⟩
  icases (own_op γ _ _).1 $$ H with ⟨Ha, Hf⟩
  iexists γ
  unfold server
  simp only [↓reduceIte]
  isplitl []
  · istop; exact internalEq.refl
  isplitl [Ha]
  · iexact Ha
  · iexact Hf

theorem server_0_empty (γ : GName) (x : A) : server (GF := GF) γ 0 x ⊢ x ≡ UCMRA.unit := by
  unfold server
  simp only [↓reduceIte]
  iintro ⟨H, _⟩
  iexact H

theorem server_1_agree (γ : GName) (x y : A) :
    server (GF := GF) γ 1 x ⊢ client γ y -∗ ⌜x = y⌝ := by
  unfold server client
  simp only [Nat.one_ne_zero, ↓reduceIte]
  iintro Hs Hc
  icases (own_valid_pure_2 γ _ _) $$ Hs Hc with %Hv
  ipureintro
  obtain ⟨hinc, _⟩ := Auth.auth_both_valid_discrete.mp Hv
  rcases contribCl_inc _ _ _ _ hinc with ⟨_, h⟩ | ⟨r, hr, _⟩
  · exact h
  · exact absurd hr.symm (positive_add_ne_self _ _)

theorem server_valid (γ : GName) (n : Nat) (x : A) : server (GF := GF) γ n x ⊢ ⌜✓ x⌝ := by
  unfold server
  split
  · iintro ⟨H, _⟩
    ihave H := discrete_eq_mp $$ H
    icases H with %H
    ipureintro
    subst H; exact UCMRA.unit_valid
  · iintro Hs
    icases (own_valid_pure γ _) $$ Hs with %Hv
    ipureintro
    exact (contribCl_valid _ _).mp (Auth.auth_valid.mp Hv)

theorem client_valid (γ : GName) (x : A) : client (GF := GF) γ x ⊢ ⌜✓ x⌝ := by
  unfold client
  iintro Hs
  icases (own_valid_pure γ _) $$ Hs with %Hv
  ipureintro
  exact (contribCl_valid _ _).mp (Auth.frag_valid.mp Hv)

theorem server_agree (γ : GName) (n : Nat) (x y : A) :
    server (GF := GF) γ n x ⊢ client γ y -∗ ⌜n ≠ 0 ∧ y ≼ x⌝ := by
  unfold server client
  split
  · iintro ⟨_, _, Hc'⟩ Hc
    icases (own_valid_pure_2 γ _ _) $$ Hc Hc' with %Hv
    ipureintro
    exact (Auth.frag_op_valid.mp Hv).elim
  · rename_i hn
    iintro Hs Hc
    icases (own_valid_pure_2 γ _ _) $$ Hs Hc with %Hv
    ipureintro
    obtain ⟨hinc, _⟩ := Auth.auth_both_valid_discrete.mp Hv
    refine ⟨hn, ?_⟩
    rcases contribCl_inc _ _ _ _ hinc with ⟨_, h⟩ | ⟨r, _, h⟩
    · subst h; exact CMRA.inc_refl _
    · exact h

theorem server_agree' (γ : GName) (n : Nat) (x y : A) :
    server (GF := GF) γ n x ∗ client γ y ⊢ (server γ n x ∗ client γ y) ∗ ⌜n ≠ 0 ∧ y ≼ x⌝ :=
  persistent_entails_left ((sep_mono_left (server_agree γ n x y)).trans wand_elim_left)

theorem server_1_agree' (γ : GName) (x y : A) :
    server (GF := GF) γ 1 x ∗ client γ y ⊢ (server γ 1 x ∗ client γ y) ∗ ⌜x = y⌝ :=
  persistent_entails_left ((sep_mono_left (server_1_agree γ x y)).trans wand_elim_left)

theorem alloc_client (γ : GName) (n : Nat) (x : A) :
    server (GF := GF) γ n x ⊢ |==> (server γ (n + 1) x ∗ client γ (UCMRA.unit : A)) := by
  by_cases hn : n = 0
  · subst hn
    unfold server client
    simp only [↓reduceIte, Nat.zero_add, Nat.one_ne_zero]
    iintro ⟨Hx, Ha, Hf⟩
    icases discrete_eq_mp $$ Hx with %Hx
    subst Hx
    have hlu : ((contribCr (A := A)), (contribCr (A := A))) ~l~>
        (contribCl (positive.ofNat 1) UCMRA.unit, contribCl positive.one UCMRA.unit) :=
      LocalUpdate.option (LocalUpdate.exclusive ⟨trivial, UCMRA.unit_valid⟩)
    iapply (BIUpdate.mono (own_op γ _ _).1)
    iapply (own_update_2 γ _ _ _ (Auth.auth_update hlu)) $$ Ha Hf
  · unfold server client
    simp only [hn, ↓reduceIte, Nat.add_one_ne_zero]
    have e1 : contribCl positive.one (UCMRA.unit : A) • contribCl (positive.ofNat n) x =
        contribCl (positive.ofNat (n + 1)) x := by
      rw [contribCl_op, UCMRA.unit_left_id]
      congr 3; ext; simp [positive.ofNat, positive.one]; omega
    have hlu : (contribCl (positive.ofNat n) x, (UCMRA.unit : ContribT A)) ~l~>
        (contribCl (positive.ofNat (n + 1)) x, contribCl positive.one (UCMRA.unit : A)) := by
      have := LocalUpdate.op_discrete (contribCl (positive.ofNat n) x) UCMRA.unit
        (contribCl positive.one (UCMRA.unit : A))
        (fun h => (contribCl_valid _ _).mpr (by
          rw [UCMRA.unit_left_id]; exact (contribCl_valid _ _).mp h))
      rwa [e1, CMRA.unit_right_id] at this
    exact (own_update γ _ _ (Auth.auth_update_alloc hlu)).trans (BIUpdate.mono (own_op γ _ _).1)

theorem dealloc_client (γ : GName) (n : Nat) (x : A) :
    server (GF := GF) γ n x ⊢ client γ (UCMRA.unit : A) ==∗ server γ (n - 1) x := by
  iintro Hs Hc
  by_cases hn1 : n = 1
  · subst hn1
    icases (server_1_agree' γ x UCMRA.unit) $$ [Hs Hc] with ⟨⟨Hs, Hc⟩, %Hx⟩
    · isplitl [Hs]
      · iexact Hs
      · iexact Hc
    subst Hx
    unfold server client
    simp only [Nat.one_ne_zero, ↓reduceIte, Nat.sub_self]
    have hlu : (contribCl (positive.ofNat 1) (UCMRA.unit : A), contribCl positive.one (UCMRA.unit : A)) ~l~>
        ((contribCr (A := A)), (contribCr (A := A))) := by
      refine (LocalUpdate.discrete _ _ _ _).mpr fun mz _ he => ⟨trivial, ?_⟩
      rcases mz with _ | z
      · rfl
      · rcases contribCl_op_eq _ _ _ _ z he with ⟨_, _, rfl⟩ | ⟨r, w, hr, _, _⟩
        · rfl
        · exact absurd hr.symm (positive_add_ne_self _ _)
    iapply (BIUpdate.mono ?_)
    rotate_left
    · iapply (own_update_2 γ _ _ _ (Auth.auth_update hlu)) $$ Hs Hc
    iintro H
    icases (own_op γ _ _).1 $$ H with ⟨Ha, Hf⟩
    isplitl []
    · istop; exact internalEq.refl
    isplitl [Ha]
    · iexact Ha
    · iexact Hf
  · icases (server_agree' γ n x UCMRA.unit) $$ [Hs Hc] with ⟨⟨Hs, Hc⟩, %Hag⟩
    · isplitl [Hs]
      · iexact Hs
      · iexact Hc
    obtain ⟨hn0, _⟩ := Hag
    unfold server client
    have hn' : n - 1 ≠ 0 := by omega
    simp only [hn0, hn', ↓reduceIte]
    have hlu : (contribCl (positive.ofNat n) x, contribCl positive.one (UCMRA.unit : A)) ~l~>
        (contribCl (positive.ofNat (n - 1)) x, (UCMRA.unit : ContribT A)) := by
      refine (LocalUpdate.discrete _ _ _ _).mpr fun mz hv he => ?_
      rcases mz with _ | z
      · exfalso
        have he' : contribCl (positive.ofNat n) x = contribCl positive.one (UCMRA.unit : A) := he
        have := congrArg (fun z : ContribT A => match z with
          | some (.inl (q, _)) => q.pred | _ => 0) he'
        simp [positive.ofNat, positive.one] at this; omega
      · rcases contribCl_op_eq _ _ _ _ z he with ⟨h1, _, _⟩ | ⟨r, w, hr, hw, rfl⟩
        · have := congrArg positive.pred h1; simp [positive.ofNat, positive.one] at this; omega
        · rw [UCMRA.unit_left_id] at hw
          subst hw
          refine ⟨(contribCl_valid _ _).mpr ((contribCl_valid _ _).mp hv), ?_⟩
          show contribCl (positive.ofNat (n - 1)) x = (UCMRA.unit : ContribT A) • contribCl r x
          rw [UCMRA.unit_left_id]
          congr 3; ext
          have := congrArg positive.pred hr
          simp [positive.ofNat, positive.one] at this ⊢; omega
    iapply (own_update_2 γ _ _ _ (Auth.auth_update_dealloc hlu)) $$ Hs Hc

theorem update_client (γ : GName) (n : Nat) (x y x' y' : A) (Hup : (x, y) ~l~> (x', y')) :
    server (GF := GF) γ n x ⊢ client γ y ==∗ server γ n x' ∗ client γ y' := by
  iintro Hs Hc
  icases (server_agree' γ n x y) $$ [Hs Hc] with ⟨⟨Hs, Hc⟩, %Hag⟩
  · isplitl [Hs]
    · iexact Hs
    · iexact Hc
  obtain ⟨hn0, _⟩ := Hag
  unfold server client
  simp only [hn0, ↓reduceIte]
  have hlu : (contribCl (positive.ofNat n) x, contribCl positive.one y) ~l~>
      (contribCl (positive.ofNat n) x', contribCl positive.one y') :=
    LocalUpdate.option (Csum.local_update_l (LocalUpdate.prod_2 _ _ Hup))
  iapply (BIUpdate.mono (own_op γ _ _).1)
  iapply (own_update_2 γ _ _ _ (Auth.auth_update hlu)) $$ Hs Hc

/-! ### Derived -/

theorem contribution_init_pow (n : Nat) :
    ⊢ |==> ∃ γ, server (GF := GF) γ n (UCMRA.unit : A) ∗
      [∗list] _k ↦ P ∈ List.replicate n (client (GF := GF) γ (UCMRA.unit : A)), P := by
  induction n with
  | zero =>
    refine (contribution_init (GF := GF) (A := A)).trans (BIUpdate.mono (exists_mono fun γ => ?_))
    rw [List.replicate_zero]
    iintro Hs
    isplitl [Hs]
    · iexact Hs
    · istop; exact BigSepL.bigSepL_nil.2
  | succ n ih =>
    refine ih.trans ((BIUpdate.mono (exists_elim fun γ => ?_)).trans BIUpdate.trans)
    refine (sep_mono_left (alloc_client γ n UCMRA.unit)).trans (bupd_frame_right.trans
      (BIUpdate.mono ?_))
    iintro ⟨⟨Hs, Hc⟩, Hl⟩
    iexists γ
    rw [show List.replicate (n + 1) (client (GF := GF) γ (UCMRA.unit : A)) =
      client γ UCMRA.unit :: List.replicate n (client γ UCMRA.unit) from rfl]
    isplitl [Hs]
    · iexact Hs
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hc]
      · iexact Hc
      · iexact Hl

theorem server_client_op_false (γ : GName) (x y1 y2 : A) :
    server (GF := GF) γ 1 x ⊢ client γ y1 -∗ client γ y2 -∗ False := by
  unfold server client
  simp only [Nat.one_ne_zero, ↓reduceIte]
  iintro Hs Hc1 Hc2
  ihave Hc := (own_op γ _ _).2 $$ [Hc1 Hc2]
  · isplitl [Hc1]
    · iexact Hc1
    · iexact Hc2
  icases (own_valid_pure_2 γ _ _) $$ Hs Hc with %Hv
  ipureintro
  obtain ⟨hinc, _⟩ := Auth.auth_both_valid_discrete.mp Hv
  rw [contribCl_op] at hinc
  rcases contribCl_inc _ _ _ _ hinc with ⟨h, _⟩ | ⟨r, hr, _⟩
  · exact absurd (congrArg positive.pred h) (by simp [positive.ofNat, positive.one])
  · have := congrArg positive.pred hr; simp [positive.ofNat, positive.one] at this

end contribution

end Perennial
