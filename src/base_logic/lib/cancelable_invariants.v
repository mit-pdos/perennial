From iris.algebra Require Export frac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From Perennial.base_logic.lib Require Export invariants.
From iris.prelude Require Import options.
Import uPred.

Class cinvG Σ := cinv_inG :> inG Σ fracR.
Definition cinvΣ : gFunctors := #[GFunctor fracR].

Global Instance subG_cinvΣ {Σ} : subG cinvΣ Σ → cinvG Σ.
Proof. solve_inG. Qed.

Section defs.
  Context `{!invG Σ, !cinvG Σ}.

  Definition cinv_own (γ : gname) (p : frac) : iProp Σ := own γ p.

  Definition cinv (N : namespace) (γ : gname) (P : iProp Σ) : iProp Σ :=
    inv N (P ∨ cinv_own γ 1).
End defs.

Global Instance: Params (@cinv) 5 := {}.

Section proofs.
  Context `{!invG Σ, !cinvG Σ}.

  Global Instance cinv_own_timeless γ p : Timeless (cinv_own γ p).
  Proof. rewrite /cinv_own; apply _. Qed.

  Global Instance cinv_contractive N γ : Contractive (cinv N γ).
  Proof. solve_contractive. Qed.
  Global Instance cinv_ne N γ : NonExpansive (cinv N γ).
  Proof. exact: contractive_ne. Qed.
  Global Instance cinv_proper N γ : Proper ((≡) ==> (≡)) (cinv N γ).
  Proof. exact: ne_proper. Qed.

  Global Instance cinv_persistent N γ P : Persistent (cinv N γ P).
  Proof. rewrite /cinv; apply _. Qed.

  Global Instance cinv_own_fractional γ : Fractional (cinv_own γ).
  Proof. intros ??. by rewrite /cinv_own -own_op. Qed.
  Global Instance cinv_own_as_fractional γ q :
    AsFractional (cinv_own γ q) (cinv_own γ) q.
  Proof. split; [done|]. apply _. Qed.

  Lemma cinv_own_valid γ q1 q2 : cinv_own γ q1 -∗ cinv_own γ q2 -∗ ⌜q1 + q2 ≤ 1⌝%Qp.
  Proof. rewrite -frac_validI. apply (own_valid_2 γ q1 q2). Qed.

  Lemma cinv_own_1_l γ q : cinv_own γ 1 -∗ cinv_own γ q -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (cinv_own_valid with "H1 H2") as %[]%(exclusive_l 1%Qp).
  Qed.

  Lemma cinv_iff N γ P Q : cinv N γ P -∗ ▷ □ (P ↔ Q) -∗ cinv N γ Q.
  Proof.
    iIntros "HI #HPQ". iApply (inv_iff with "HI"). iIntros "!> !>".
    iSplit; iIntros "[?|$]"; iLeft; by iApply "HPQ".
  Qed.

  (*** Allocation rules. *)
  (** The "strong" variants permit any infinite [I], and choosing [P] is delayed
  until after [γ] was chosen.*)
  Lemma cinv_alloc_strong (I : gname → Prop) E N :
    pred_infinite I →
    ⊢ |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ cinv_own γ 1 ∗ ∀ P, ▷ P ={E}=∗ cinv N γ P.
  Proof.
    iIntros (?). iMod (own_alloc_strong 1%Qp I) as (γ) "[Hfresh Hγ]"; [done|done|].
    iExists γ. iIntros "!> {$Hγ $Hfresh}" (P) "HP".
    iMod (inv_alloc N _ (P ∨ cinv_own γ 1) with "[HP]"); eauto.
  Qed.

  (** The "open" variants create the invariant in the open state, and delay
  having to prove [P].
  These do not imply the other variants because of the extra assumption [↑N ⊆ E]. *)
  Lemma cinv_alloc_strong_open (I : gname → Prop) E N :
    pred_infinite I →
    ↑N ⊆ E →
    ⊢ |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ cinv_own γ 1 ∗ ∀ P,
      |={E,E∖↑N}=> cinv N γ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (??). iMod (own_alloc_strong 1%Qp I) as (γ) "[Hfresh Hγ]"; [done|done|].
    iExists γ. iIntros "!> {$Hγ $Hfresh}" (P).
    iMod (inv_alloc_open N _ (P ∨ cinv_own γ 1)) as "[Hinv Hclose]"; first by eauto.
    iIntros "!>". iFrame. iIntros "HP". iApply "Hclose". iLeft. done.
  Qed.

  Lemma cinv_alloc_cofinite (G : gset gname) E N :
    ⊢ |={E}=> ∃ γ, ⌜ γ ∉ G ⌝ ∗ cinv_own γ 1 ∗ ∀ P, ▷ P ={E}=∗ cinv N γ P.
  Proof.
    apply cinv_alloc_strong. apply (pred_infinite_set (C:=gset gname))=> E'.
    exists (fresh (G ∪ E')). apply not_elem_of_union, is_fresh.
  Qed.

  Lemma cinv_alloc E N P : ▷ P ={E}=∗ ∃ γ, cinv N γ P ∗ cinv_own γ 1.
  Proof.
    iIntros "HP". iMod (cinv_alloc_cofinite ∅ E N) as (γ _) "[Hγ Halloc]".
    iExists γ. iFrame "Hγ". by iApply "Halloc".
  Qed.

  Lemma cinv_alloc_open E N P :
    ↑N ⊆ E → ⊢ |={E,E∖↑N}=> ∃ γ, cinv N γ P ∗ cinv_own γ 1 ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?). iMod (cinv_alloc_strong_open (λ _, True)) as (γ) "(_ & Htok & Hmake)"; [|done|].
    { apply pred_infinite_True. }
    iMod ("Hmake" $! P) as "[Hinv Hclose]". iIntros "!>". iExists γ. iFrame.
  Qed.

  (*** Accessors *)
  Lemma cinv_acc_strong E N γ p P :
    ↑N ⊆ E →
    cinv N γ P -∗ (cinv_own γ p ={E,E∖↑N}=∗
    ▷ P ∗ cinv_own γ p ∗ (∀ E' : coPset, ▷ P ∨ cinv_own γ 1 ={E',↑N ∪ E'}=∗ True)).
  Proof.
    iIntros (?) "Hinv Hown".
    iPoseProof (inv_acc (↑ N) N with "Hinv") as "H"; first done.
    rewrite difference_diag_L.
    iPoseProof (fupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
    rewrite left_id_L -union_difference_L //. iMod "H" as "[[$ | >Hown'] H]".
    - iIntros "{$Hown} !>" (E') "HP".
      iPoseProof (fupd_mask_frame_r _ _ E' with "(H [HP])") as "H"; first set_solver.
      { iDestruct "HP" as "[?|?]"; eauto. }
      by rewrite left_id_L.
    - iDestruct (cinv_own_1_l with "Hown' Hown") as %[].
  Qed.

  Lemma cinv_acc E N γ p P :
    ↑N ⊆ E →
    cinv N γ P -∗ cinv_own γ p ={E,E∖↑N}=∗ ▷ P ∗ cinv_own γ p ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "#Hinv Hγ".
    iMod (cinv_acc_strong with "Hinv Hγ") as "($ & $ & H)"; first done.
    iIntros "!> HP".
    rewrite {2}(union_difference_L (↑N) E)=> //.
    iApply "H". by iLeft.
  Qed.

  (*** Other *)
  Lemma cinv_cancel E N γ P : ↑N ⊆ E → cinv N γ P -∗ cinv_own γ 1 ={E}=∗ ▷ P.
  Proof.
    iIntros (?) "#Hinv Hγ".
    iMod (cinv_acc_strong with "Hinv Hγ") as "($ & Hγ & H)"; first done.
    rewrite {2}(union_difference_L (↑N) E)=> //.
    iApply "H". by iRight.
  Qed.

  Global Instance into_inv_cinv N γ P : IntoInv (cinv N γ P) N := {}.

  Global Instance into_acc_cinv E N γ P p :
    IntoAcc (X:=unit) (cinv N γ P)
            (↑N ⊆ E) (cinv_own γ p) (fupd E (E∖↑N)) (fupd (E∖↑N) E)
            (λ _, ▷ P ∗ cinv_own γ p)%I (λ _, ▷ P)%I (λ _, None)%I.
  Proof.
    rewrite /IntoAcc /accessor. iIntros (?) "#Hinv Hown".
    rewrite exist_unit -assoc.
    iApply (cinv_acc with "Hinv"); done.
  Qed.
End proofs.

Typeclasses Opaque cinv_own cinv.
