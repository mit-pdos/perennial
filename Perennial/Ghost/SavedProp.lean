/-
Port of `new/ghost/saved_prop.v`: saved propositions and saved predicates on top of
the universal `own` (see `Perennial/Ghost/All.lean`).

`saved_prop_own γ dq P` owns `(dq, toAgree (Next P))` in `DFrac × Agree (Later (IProp GF))`
(code `prodR dfracR (agreeR laterO)`). `saved_pred_own γ dq Φ` for `Φ : A → IProp GF` with
`[Pos.Countable A]` stores `Φ ∘ decode : Pos → Later (IProp GF)` (code
`prodR dfracR (agreeR (discrete_funO pos laterO))`), since the codes cannot mention `A`.
-/
import Perennial.Ghost.Own
import Perennial.Ghost.Countable

noncomputable section

namespace Perennial
open Iris BI OFE CMRA ProofMode COFE Agree Iris.Std

variable {GF : BundledGFunctors} [allG GF]

/-! ## Generic layer: `dfrac_agree` over a coded OFE -/
section saved_anything
variable {T : Type} [OFE T] {o : Syntax.ofe} [IsOfe (IProp GF) T o]

/-- Shared implementation of saved props/preds: own `to_dfrac_agree dq x`. -/
def saved_anything_own (γ : GName) (dq : DFrac) (x : T) : IProp GF :=
  own γ (DFracAgree.mk dq x)

instance saved_anything_discarded_persistent (γ : GName) (x : T) :
    Persistent (saved_anything_own (GF := GF) γ .discard x) := by
  unfold saved_anything_own; infer_instance

instance saved_anything_ne (γ : GName) (dq : DFrac) :
    NonExpansive (saved_anything_own (GF := GF) (T := T) γ dq) where
  ne _ _ _ H := (own_ne γ).ne (DFracAgree.mk_ne.ne H)

instance saved_anything_fractional (γ : GName) (x : T) :
    Fractional (fun q : Qp => saved_anything_own (GF := GF) γ (.own q) x) where
  fractional p q := by
    unfold saved_anything_own
    rw [DFracAgree.Frac.mk_op (q₁ := p) (q₂ := q) |> fun h => (show DFracAgree.mk (.own (p + q)) x =
      DFracAgree.mk (.own p) x • DFracAgree.mk (.own q) x from h)]
    exact own_op γ _ _

theorem saved_anything_alloc_strong (x : T) (I : GName → Prop) (dq : DFrac)
    (Hdq : ✓ dq) (HI : PredInfinite I) :
    ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_anything_own (GF := GF) γ dq x :=
  own_alloc_strong _ I HI ⟨Hdq, toAgree_valid⟩

theorem saved_anything_alloc_cofinite (x : T) (G : List GName) (dq : DFrac) (Hdq : ✓ dq) :
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_anything_own (GF := GF) γ dq x :=
  own_alloc_cofinite _ G ⟨Hdq, toAgree_valid⟩

theorem saved_anything_alloc (x : T) (dq : DFrac) (Hdq : ✓ dq) :
    ⊢ |==> ∃ γ, saved_anything_own (GF := GF) γ dq x :=
  own_alloc _ ⟨Hdq, toAgree_valid⟩

theorem saved_anything_valid (γ : GName) (dq : DFrac) (x : T) :
    saved_anything_own (GF := GF) γ dq x ⊢ ⌜✓ dq⌝ :=
  (own_valid γ _).trans (dfrac_agree_validI dq x).mp

theorem saved_anything_valid_2 (γ : GName) (dq1 dq2 : DFrac) (x y : T) :
    saved_anything_own (GF := GF) γ dq1 x ∗ saved_anything_own γ dq2 y ⊢
      ⌜✓ (dq1 • dq2)⌝ ∧ internalEq x y :=
  ((own_op γ _ _).2.trans (own_valid γ _)).trans (dfrac_agree_validI_2 dq1 dq2 x y).mp

theorem saved_anything_persist (γ : GName) (dq : DFrac) (x : T) :
    saved_anything_own (GF := GF) γ dq x ⊢ |==> saved_anything_own γ .discard x :=
  own_update γ _ _ DFracAgree.persist

theorem saved_anything_unpersist (γ : GName) (x : T) :
    saved_anything_own (GF := GF) γ .discard x ⊢ |==> ∃ q, saved_anything_own γ (.own q) x := by
  unfold saved_anything_own
  refine (own_updateP _ γ _ DFracAgree.unpersist).trans (BIUpdate.mono ?_)
  iintro ⟨%a', %hq, Ha⟩
  obtain ⟨q, rfl⟩ := hq
  iexists q
  iexact Ha

theorem saved_anything_update (y : T) (γ : GName) (x : T) :
    saved_anything_own (GF := GF) γ (.own 1) x ⊢ |==> saved_anything_own γ (.own 1) y :=
  haveI : Exclusive (DFracAgree.mk (.own (1 : Qp)) x) := DFracAgree.mk_exclusive
  own_update γ _ _ (Update.exclusive ⟨DFrac.valid_own_one, toAgree_valid⟩)

theorem saved_anything_update_2 (y : T) (γ : GName) (q1 q2 : Qp) (x1 x2 : T)
    (Hq : q1 + q2 = 1) :
    saved_anything_own (GF := GF) γ (.own q1) x1 ∗ saved_anything_own γ (.own q2) x2 ⊢ |==>
      (saved_anything_own γ (.own q1) y ∗ saved_anything_own γ (.own q2) y) := by
  unfold saved_anything_own
  have hupd : DFracAgree.mk (.own q1) x1 • DFracAgree.mk (.own q2) x2 ~~>
      DFracAgree.mk (.own q1) y • DFracAgree.mk (.own q2) y :=
    DFracAgree.update₂ (show DFrac.own q1 • DFrac.own q2 = DFrac.own 1 from congrArg DFrac.own Hq)
  exact ((own_op γ _ _).2.trans (own_update γ _ _ hupd)).trans (BIUpdate.mono (own_op γ _ _).1)

end saved_anything

/-! ## Saved propositions -/
section saved_prop

def saved_prop_own (γ : GName) (dq : DFrac) (P : IProp GF) : IProp GF :=
  saved_anything_own γ dq (Later.next P)

instance saved_prop_discarded_persistent (γ : GName) (P : IProp GF) :
    Persistent (saved_prop_own γ .discard P) := by
  unfold saved_prop_own; infer_instance

instance saved_prop_own_contractive (γ : GName) (dq : DFrac) :
    Contractive (saved_prop_own (GF := GF) γ dq) :=
  ⟨fun {_ _ _} h => (saved_anything_ne γ dq).ne (NextContractive.distLater_dist h)⟩

instance saved_prop_ne (γ : GName) (dq : DFrac) : NonExpansive (saved_prop_own (GF := GF) γ dq) :=
  inferInstance

instance saved_prop_fractional (γ : GName) (P : IProp GF) :
    Fractional (fun q : Qp => saved_prop_own γ (.own q) P) := by
  unfold saved_prop_own; infer_instance

instance saved_prop_as_fractional (γ : GName) (P : IProp GF) (q : Qp) :
    AsFractional (saved_prop_own γ (.own q) P) ioΦ (fun q => saved_prop_own γ (.own q) P) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := saved_prop_fractional γ P

/-! Allocation -/

theorem saved_prop_alloc_strong (P : IProp GF) (I : GName → Prop) (dq : DFrac)
    (Hdq : ✓ dq) (HI : PredInfinite I) :
    ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_prop_own γ dq P :=
  saved_anything_alloc_strong _ I dq Hdq HI

theorem saved_prop_alloc_cofinite (P : IProp GF) (G : List GName) (dq : DFrac) (Hdq : ✓ dq) :
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_prop_own γ dq P :=
  saved_anything_alloc_cofinite _ G dq Hdq

theorem saved_prop_alloc (P : IProp GF) (dq : DFrac) (Hdq : ✓ dq) :
    ⊢ |==> ∃ γ, saved_prop_own γ dq P :=
  saved_anything_alloc _ dq Hdq

/-! Validity -/

theorem saved_prop_valid (γ : GName) (dq : DFrac) (P : IProp GF) :
    ⊢ saved_prop_own γ dq P -∗ ⌜✓ dq⌝ :=
  entails_wand (saved_anything_valid γ dq _)

theorem saved_prop_valid_2 (γ : GName) (dq1 dq2 : DFrac) (P Q : IProp GF) :
    ⊢ saved_prop_own γ dq1 P -∗ saved_prop_own γ dq2 Q -∗ ⌜✓ (dq1 • dq2)⌝ ∗ ▷ (P ≡ Q) :=
  entails_wand <| wand_intro <|
    ((saved_anything_valid_2 γ dq1 dq2 (Later.next P) (Later.next Q)).trans
      (and_mono_right (later_equivI P Q).mp)).trans persistent_and_sep_mp

theorem saved_prop_agree (γ : GName) (dq1 dq2 : DFrac) (P Q : IProp GF) :
    ⊢ saved_prop_own γ dq1 P -∗ saved_prop_own γ dq2 Q -∗ ▷ (P ≡ Q) := by
  iintro Hx Hy
  ihave ⟨-, $⟩ := saved_prop_valid_2 γ dq1 dq2 P Q $$ Hx Hy

/-- Higher cost than the `Fractional` instance, which kicks in for `#q`s. -/
instance (priority := default - 50) saved_prop_combine_as (γ : GName) (dq1 dq2 : DFrac)
    (P Q : IProp GF) :
    CombineSepAs (saved_prop_own γ dq1 P) (saved_prop_own γ dq2 Q)
      (saved_prop_own γ (dq1 • dq2) P) where
  combine_sep_as := by
    refine (and_intro ((saved_anything_valid_2 γ dq1 dq2 (Later.next P) (Later.next Q)).trans
      and_elim_r) .rfl).trans ?_
    haveI : NonExpansive (fun y : Later (IProp GF) =>
        iprop(saved_anything_own (GF := GF) γ dq1 (Later.next P) ∗ saved_anything_own γ dq2 y)) :=
      ⟨fun _ _ _ h => BI.sep_ne.ne .rfl ((saved_anything_ne γ dq2).ne h)⟩
    refine (internalEq.rewrite' (a := Later.next Q) (b := Later.next P)
      (fun y => iprop(saved_anything_own (GF := GF) γ dq1 (Later.next P) ∗
        saved_anything_own γ dq2 y)) (and_elim_l.trans internalEq.symm) and_elim_r).trans ?_
    unfold saved_prop_own saved_anything_own
    rw [DFracAgree.mk_op]
    exact (own_op γ _ _).2

instance saved_prop_combine_gives (γ : GName) (dq1 dq2 : DFrac) (P Q : IProp GF) :
    CombineSepGives (saved_prop_own γ dq1 P) (saved_prop_own γ dq2 Q)
      iprop(⌜✓ (dq1 • dq2)⌝ ∗ ▷ (P ≡ Q)) where
  combine_sep_gives := by
    iintro ⟨Hx, Hy⟩
    ihave H := saved_prop_valid_2 γ dq1 dq2 P Q $$ Hx Hy
    icases H with ⟨%Hv, #Heq⟩
    imodintro
    isplit
    · ipureintro; exact Hv
    · iexact Heq

/-! Make an element read-only -/

theorem saved_prop_persist (γ : GName) (dq : DFrac) (P : IProp GF) :
    ⊢ saved_prop_own γ dq P ==∗ saved_prop_own γ .discard P :=
  entails_wand (saved_anything_persist γ dq _)

/-- Recover fractional ownership for read-only element. -/
theorem saved_prop_unpersist (γ : GName) (P : IProp GF) :
    ⊢ saved_prop_own γ .discard P ==∗ ∃ q, saved_prop_own γ (.own q) P :=
  entails_wand (saved_anything_unpersist γ _)

/-! Updates -/

theorem saved_prop_update (Q : IProp GF) (γ : GName) (P : IProp GF) :
    ⊢ saved_prop_own γ (.own 1) P ==∗ saved_prop_own γ (.own 1) Q :=
  entails_wand (saved_anything_update _ γ _)

theorem saved_prop_update_2 (Q : IProp GF) (γ : GName) (q1 q2 : Qp) (P1 P2 : IProp GF)
    (Hq : q1 + q2 = 1) :
    ⊢ saved_prop_own γ (.own q1) P1 -∗ saved_prop_own γ (.own q2) P2 ==∗
      saved_prop_own γ (.own q1) Q ∗ saved_prop_own γ (.own q2) Q :=
  entails_wand (wand_intro (saved_anything_update_2 _ γ q1 q2 _ _ Hq))

theorem saved_prop_update_halves (Q : IProp GF) (γ : GName) (P1 P2 : IProp GF) :
    ⊢ saved_prop_own γ (.own (Qp.half 1)) P1 -∗ saved_prop_own γ (.own (Qp.half 1)) P2 ==∗
      saved_prop_own γ (.own (Qp.half 1)) Q ∗ saved_prop_own γ (.own (Qp.half 1)) Q :=
  saved_prop_update_2 Q γ _ _ P1 P2 (Qp.half_add_half 1)

end saved_prop

/-! ## Saved predicates -/
section saved_pred
variable {A : Type} [Pos.Countable A]

/-- The stored function: `Next ∘ Φ ∘ decode` (`False` outside the image of `encode`). -/
def saved_pred_fn (Φ : A → IProp GF) (p : Pos) : Later (IProp GF) :=
  Later.next (match (Pos.Countable.decode p : Option A) with | some a => Φ a | none => iprop(False))

theorem saved_pred_fn_encode (Φ : A → IProp GF) (a : A) :
    saved_pred_fn Φ (Pos.Countable.encode a) = Later.next (Φ a) := by
  simp [saved_pred_fn, Pos.Countable.decode_encode]

def saved_pred_own (γ : GName) (dq : DFrac) (Φ : A → IProp GF) : IProp GF :=
  saved_anything_own γ dq (saved_pred_fn Φ)

instance saved_pred_discarded_persistent (γ : GName) (Φ : A → IProp GF) :
    Persistent (saved_pred_own γ .discard Φ) := by
  unfold saved_pred_own; infer_instance

instance saved_pred_own_contractive (γ : GName) (dq : DFrac) :
    Contractive (saved_pred_own (GF := GF) (A := A) γ dq) :=
  ⟨fun {_ Φ Ψ} h => (saved_anything_ne γ dq).ne fun p => by
    unfold saved_pred_fn
    cases (Pos.Countable.decode p : Option A) with
    | none => exact .rfl
    | some a => exact NextContractive.distLater_dist (fun m hm => h m hm a)⟩

instance saved_pred_fractional (γ : GName) (Φ : A → IProp GF) :
    Fractional (fun q : Qp => saved_pred_own γ (.own q) Φ) := by
  unfold saved_pred_own; infer_instance

instance saved_pred_as_fractional (γ : GName) (Φ : A → IProp GF) (q : Qp) :
    AsFractional (saved_pred_own γ (.own q) Φ) ioΦ (fun q => saved_pred_own γ (.own q) Φ) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := saved_pred_fractional γ Φ

/-! Allocation -/

theorem saved_pred_alloc_strong (Φ : A → IProp GF) (I : GName → Prop) (dq : DFrac)
    (Hdq : ✓ dq) (HI : PredInfinite I) :
    ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_pred_own γ dq Φ :=
  saved_anything_alloc_strong _ I dq Hdq HI

theorem saved_pred_alloc_cofinite (Φ : A → IProp GF) (G : List GName) (dq : DFrac) (Hdq : ✓ dq) :
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_pred_own γ dq Φ :=
  saved_anything_alloc_cofinite _ G dq Hdq

theorem saved_pred_alloc (Φ : A → IProp GF) (dq : DFrac) (Hdq : ✓ dq) :
    ⊢ |==> ∃ γ, saved_pred_own γ dq Φ :=
  saved_anything_alloc _ dq Hdq

/-! Validity -/

theorem saved_pred_valid (γ : GName) (dq : DFrac) (Φ : A → IProp GF) :
    ⊢ saved_pred_own γ dq Φ -∗ ⌜✓ dq⌝ :=
  entails_wand (saved_anything_valid γ dq _)

private theorem saved_pred_fn_equivI (Φ Ψ : A → IProp GF) (x : A) :
    internalEq (saved_pred_fn Φ) (saved_pred_fn Ψ) ⊢@{IProp GF} ▷ (Φ x ≡ Ψ x) := by
  refine ((discreteFun_equivI _ _).mp.trans (forall_elim (Pos.Countable.encode x))).trans ?_
  rw [saved_pred_fn_encode, saved_pred_fn_encode]
  exact (later_equivI (Φ x) (Ψ x)).mp

theorem saved_pred_valid_2 (γ : GName) (dq1 dq2 : DFrac) (Φ Ψ : A → IProp GF) (x : A) :
    ⊢ saved_pred_own γ dq1 Φ -∗ saved_pred_own γ dq2 Ψ -∗ ⌜✓ (dq1 • dq2)⌝ ∗ ▷ (Φ x ≡ Ψ x) :=
  entails_wand <| wand_intro <|
    ((saved_anything_valid_2 γ dq1 dq2 _ _).trans
      (and_mono_right (saved_pred_fn_equivI Φ Ψ x))).trans persistent_and_sep_mp

theorem saved_pred_agree (γ : GName) (dq1 dq2 : DFrac) (Φ Ψ : A → IProp GF) (x : A) :
    ⊢ saved_pred_own γ dq1 Φ -∗ saved_pred_own γ dq2 Ψ -∗ ▷ (Φ x ≡ Ψ x) := by
  iintro Hx Hy
  ihave ⟨-, $⟩ := saved_pred_valid_2 γ dq1 dq2 Φ Ψ x $$ Hx Hy

/-- Higher cost than the `Fractional` instance, which kicks in for `#q`s. -/
instance (priority := default - 50) saved_pred_combine_as (γ : GName) (dq1 dq2 : DFrac)
    (Φ Ψ : A → IProp GF) :
    CombineSepAs (saved_pred_own γ dq1 Φ) (saved_pred_own γ dq2 Ψ)
      (saved_pred_own γ (dq1 • dq2) Φ) where
  combine_sep_as := by
    refine (and_intro ((saved_anything_valid_2 γ dq1 dq2 (saved_pred_fn Φ) (saved_pred_fn Ψ)).trans
      and_elim_r) .rfl).trans ?_
    haveI : NonExpansive (fun y : Pos → Later (IProp GF) =>
        iprop(saved_anything_own (GF := GF) γ dq1 (saved_pred_fn Φ) ∗ saved_anything_own γ dq2 y)) :=
      ⟨fun _ _ _ h => BI.sep_ne.ne .rfl ((saved_anything_ne γ dq2).ne h)⟩
    refine (internalEq.rewrite' (a := saved_pred_fn Ψ) (b := saved_pred_fn Φ)
      (fun y => iprop(saved_anything_own (GF := GF) γ dq1 (saved_pred_fn Φ) ∗
        saved_anything_own γ dq2 y)) (and_elim_l.trans internalEq.symm) and_elim_r).trans ?_
    unfold saved_pred_own saved_anything_own
    rw [DFracAgree.mk_op]
    exact (own_op γ _ _).2

/-- Rocq states the gives-part as an equality of the stored functions
`Next ∘ Φ ≡ Next ∘ Ψ`; here the stored function is `saved_pred_fn`. -/
instance saved_pred_combine_gives (γ : GName) (dq1 dq2 : DFrac) (Φ Ψ : A → IProp GF) :
    CombineSepGives (saved_pred_own γ dq1 Φ) (saved_pred_own γ dq2 Ψ)
      iprop(⌜✓ (dq1 • dq2)⌝ ∗ internalEq (saved_pred_fn Φ) (saved_pred_fn Ψ)) where
  combine_sep_gives :=
    ((saved_anything_valid_2 γ dq1 dq2 _ _).trans persistent_and_sep_mp).trans Persistent.persistent

/-! Make an element read-only -/

theorem saved_pred_persist (γ : GName) (dq : DFrac) (Φ : A → IProp GF) :
    ⊢ saved_pred_own γ dq Φ ==∗ saved_pred_own γ .discard Φ :=
  entails_wand (saved_anything_persist γ dq _)

theorem saved_pred_unpersist (γ : GName) (Φ : A → IProp GF) :
    ⊢ saved_pred_own γ .discard Φ ==∗ ∃ q, saved_pred_own γ (.own q) Φ :=
  entails_wand (saved_anything_unpersist γ _)

/-! Updates -/

theorem saved_pred_update (Ψ : A → IProp GF) (γ : GName) (Φ : A → IProp GF) :
    ⊢ saved_pred_own γ (.own 1) Φ ==∗ saved_pred_own γ (.own 1) Ψ :=
  entails_wand (saved_anything_update _ γ _)

theorem saved_pred_update_2 (Ψ : A → IProp GF) (γ : GName) (q1 q2 : Qp) (Φ1 Φ2 : A → IProp GF)
    (Hq : q1 + q2 = 1) :
    ⊢ saved_pred_own γ (.own q1) Φ1 -∗ saved_pred_own γ (.own q2) Φ2 ==∗
      saved_pred_own γ (.own q1) Ψ ∗ saved_pred_own γ (.own q2) Ψ :=
  entails_wand (wand_intro (saved_anything_update_2 _ γ q1 q2 _ _ Hq))

theorem saved_pred_update_halves (Ψ : A → IProp GF) (γ : GName) (Φ1 Φ2 : A → IProp GF) :
    ⊢ saved_pred_own γ (.own (Qp.half 1)) Φ1 -∗ saved_pred_own γ (.own (Qp.half 1)) Φ2 ==∗
      saved_pred_own γ (.own (Qp.half 1)) Ψ ∗ saved_pred_own γ (.own (Qp.half 1)) Ψ :=
  saved_pred_update_2 Ψ γ _ _ Φ1 Φ2 (Qp.half_add_half 1)

end saved_pred

end Perennial
