From iris.algebra Require Export auth gmap frac agree excl.
From iris.bi.lib Require Import fixpoint_mono.
From iris.base_logic.lib Require Import mono_nat saved_prop.
From Perennial.goose_lang Require Import lifting.
From New.golang.theory Require Import typing.
From Perennial Require Import base.
From stdpp Require Import tactics.

Set Default Proof Using "Type".

Class simpleCrashG Σ :=
  SimpleCrashG {
      #[global] sprop_inG :: savedPropG Σ ;
      #[global] tok_inG :: inG Σ (exclR unitO) ;
  }.

Definition simpleCrashΣ := #[savedPropΣ; GFunctor (exclR unitO) ].
Global Instance subG_simpleCrashΣ {Σ} : subG (simpleCrashΣ) Σ → (simpleCrashG Σ).
Proof. solve_inG. Qed.

Section defns_and_lemmas.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context `{!simpleCrashG Σ}.
  Context (N : namespace).
  Definition own_crash_concrete P Pc : iProp Σ :=
    ∃ γprop γtok,
    saved_prop_own γprop (DfracOwn (1/2)) P ∗
      inv N (∃ Q, saved_prop_own γprop (DfracOwn (1/2)) Q ∗ (Q ∧ Pc ∨ own γtok (Excl ()) ∗ C))
  .

  Definition own_crash_pre Pc (ρ : iProp Σ → iProp Σ) (P : iProp Σ) : iProp Σ :=
    ∀ (E : coPset) (Hmask: ↑N ⊆ E), £ 2 -∗ |NC={E,E∖↑N}=> P ∗ (∀ P', (P' -∗ Pc) -∗ P' -∗ |NC={E∖↑N,E}=> ρ P').

  Definition own_crash Pc P : iProp Σ :=
    bi_greatest_fixpoint (own_crash_pre Pc) P.

  Lemma own_crash_unfold P Pc :
    own_crash Pc P -∗
    own_crash_pre Pc (own_crash Pc) P.
  Proof.
    iIntros "H".
    rewrite /own_crash.
    erewrite greatest_fixpoint_unfold.
    2:{
      constructor.
      - intros. iIntros "#Himpl * H".
        rewrite /own_crash_pre.
        iIntros (??) "Hlc".
        iMod ("H" $! _ ltac:(solve_ndisj) with "Hlc") as "[$ H]". iModIntro.
        iIntros (?) "Hwand HP'".
        iApply "Himpl".
        iApply ("H" with "[$] [$]").
      - intros.
        solve_proper.
    }
    iIntros (??) "Hlc".
    iMod ("H" $! _ ltac:(set_solver) with "Hlc") as "[$ H]".
    iIntros "!# * Hwand HP'".
    iApply ("H" with "[$] [$]").
  Qed.

  Lemma alloc_own_crash P Pc E :
    P ∧ Pc ={E}=∗ own_crash Pc P ∗ |C={↑N}=> ▷ Pc.
  Proof using Type*.
    iIntros "HP".
    iMod (saved_prop_alloc P (DfracOwn 1)) as (γprop) "[Hprop Hprop2]"; first done.
    iMod (own_alloc (Excl ())) as (γtok) "Htok"; first done.
    iMod (inv_alloc N _ (∃ Q, saved_prop_own γprop (DfracOwn (1/2)) Q ∗ (Q ∧ Pc ∨ own γtok (Excl ()) ∗ C)) with "[-Hprop Htok]") as "#Hinv".
    { iNext. iExists _; iFrame. }
    iSplitL "Hprop".
    {
      iModIntro.
      iApply (greatest_fixpoint_coiter _ (λ P, saved_prop_own γprop (DfracOwn (1/2)) P)%I).
      2:{ iFrame. }
      iIntros "!# * Hprop".
      iIntros (??) "[Hlc Hlc2]".
      rewrite ncfupd_eq.
      iIntros (?) "HNC".
      iInv "Hinv" as "Hi" "Hclose".
      iMod (lc_fupd_elim_later with "[$] Hi") as (?) "[Hprop2 Hi]".
      iDestruct (saved_prop_agree with "[$] [$]") as "#-#Hagree".
      iMod (lc_fupd_elim_later with "[$] Hagree") as "#Hagree".
      iRewrite -"Hagree".
      iDestruct "Hi" as "[Hi | [_ Hbad]]".
      2:{
        iDestruct (NC_C with "[$] [$]") as %?. done.
      }
      iDestruct "Hi" as "[$ _]".
      iFrame.
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "Hmask".
      iFrame.
      iIntros (?) "Hwand HP'".
      iIntros (?) "$".
      iMod "Hmask".
      iMod (saved_prop_update_2 with "[$] [$]") as "[$ H]".
      { rewrite Qp.half_half //. }
      iMod ("Hclose" with "[-]"); last done.
      iNext.
      iExists _; iFrame.
      iLeft. iSplit.
      { iFrame. }
      iApply "Hwand". iFrame.
    }
    iModIntro.
    iIntros "C".
    iInv "Hinv" as "Hi" "Hclose".
    iDestruct "Hi" as (?) "[? [H|>[Hbad _]]]".
    2:{ iCombine "Htok Hbad" gives %Hbad. done. }
    iDestruct "H" as "[_ $]".
    iFrame.
    iMod ("Hclose" with "[-]"); last done.
    iNext. iExists _; iFrame. iRight. iFrame.
  Qed.
End defns_and_lemmas.

Opaque own_crash.
