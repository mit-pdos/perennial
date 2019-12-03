From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From iris.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From iris.base_logic.lib Require Import wsat invariants saved_prop.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export step_fupd_extra.
Set Default Proof Using "Type".
Import uPred.

Definition crashR := csumR (exclR unitO) (agreeR unitO).
Definition NC_tok : crashR := Cinl (Excl ()).
Definition C_tok : crashR := Cinr (to_agree ()).

Class crashG Σ := { crash_inG :> inG Σ crashR; crash_name : gname }.

Definition NC_def `{crashG Σ} := own crash_name NC_tok.
Definition NC_aux `{crashG Σ} : seal NC_def. by eexists. Qed.
Definition NC `{crashG Σ} := NC_aux.(unseal).
Definition C_def `{crashG Σ} := own crash_name C_tok.
Definition C_aux `{crashG Σ} : seal C_def. by eexists. Qed.
Definition C `{crashG Σ} := C_aux.(unseal).


Class stagedG (Σ : gFunctors) : Set := WsatG {
  staging_saved_inG :> savedPropG Σ;
  staging_auth_inG :> inG Σ (authR (optionUR (exclR (prodO gnameO gnameO))));
  staging_shot_inG :> inG Σ (csumR (exclR unitO) (agreeR unitO));
}.

Definition staged_pending `{stagedG Σ} (γ: gname) : iProp Σ :=
  own γ (Cinl (Excl ())).
Definition staged_done `{stagedG Σ} (γ: gname) : iProp Σ :=
  own γ (Cinr (to_agree ())).

Definition staged_inv `{!invG Σ, !crashG Σ, !stagedG Σ} (N: namespace) k E E' (γ γ': gname) (Q: iProp Σ) : iProp Σ :=
  (inv N (∃ γprop_stored γprop_remainder Ps Pr,
             own γ (● Excl' (γprop_stored, γprop_remainder)) ∗
             saved_prop_own γprop_stored Ps ∗
             saved_prop_own γprop_remainder Pr ∗
             □ (C -∗ Ps -∗ |={E, E'}_k=> Q ∗ Pr) ∗
             (Ps ∨ (Pr ∗ C ∗ staged_done γ'))))%I.

Definition staged_value `{!stagedG Σ} (N: namespace) (γ: gname) (Q Q': iProp Σ) : iProp Σ :=
  (∃ γprop γprop', own γ (◯ Excl' (γprop, γprop')) ∗ saved_prop_own γprop Q ∗ saved_prop_own γprop' Q')%I.

Section inv.
Context `{!invG Σ, !stagedG Σ, !crashG Σ}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Σ.

Global Instance C_timeless : Timeless C.
Proof. rewrite /C C_aux.(seal_eq). apply _. Qed.

Global Instance C_persistent : Persistent C.
Proof. rewrite /C C_aux.(seal_eq). apply _. Qed.

Global Instance NC_timeless : Timeless NC.
Proof. rewrite /NC NC_aux.(seal_eq). apply _. Qed.

Global Instance staged_contractive N k E E' γ γ' : Contractive (staged_inv N k E E' γ γ').
Proof.
  rewrite /staged_inv=> n ?? ?.
  repeat (apply step_fupdN_ne || f_contractive || f_equiv); eauto.
Qed.

Global Instance staged_ne N k E E' γ γ': NonExpansive (staged_inv N k E E' γ γ').
Proof.
  rewrite /staged_inv=> n ?? ?.
  repeat (apply step_fupdN_ne || f_contractive || f_equiv); eauto using dist_le.
Qed.

Global Instance staged_proper N k E E' γ γ' : Proper ((⊣⊢) ==> (⊣⊢)) (staged_inv N k E E' γ γ').
Proof. apply ne_proper, _. Qed.

Global Instance staged_persistent N k E E' γ γ' P : Persistent (staged_inv N k E E' γ γ' P).
Proof. rewrite /staged_inv. apply _. Qed.

Lemma pending_done γ: staged_pending γ -∗ staged_done γ -∗ False.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

Lemma pending_upd_done γ: staged_pending γ ==∗ staged_done γ.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H". iMod (own_update with "H") as "$".
  { by apply cmra_update_exclusive. }
  done.
Qed.

Lemma staged_inv_iff N k E E' γ γ' P Q :
  ▷ □ (P ↔ Q) -∗
  staged_inv N k E E' γ γ' P -∗
  staged_inv N k E E' γ γ' Q.
Proof.
  iIntros "#HPQ". iApply inv_iff. iNext. iAlways. iSplit.
  - iIntros "H". iDestruct "H" as (?? P0 P0') "(?&?&?&#HP0&Hcase)". iExists _, _, P0, P0'. iFrame.
    iAlways. iIntros. iSpecialize ("HP0" with "[$] [$]"). 
    iApply (step_fupdN_inner_wand' with "HP0"); eauto.
    iIntros "(?&$)". by iApply "HPQ".
  - iIntros "H". iDestruct "H" as (?? P0 P0') "(?&?&?&#HP0&Hcase)". iExists _, _, P0, P0'. iFrame.
    iAlways. iIntros. iSpecialize ("HP0" with "[$] [$]").
    iApply (step_fupdN_inner_wand' with "HP0"); eauto.
    iIntros "(?&$)". by iApply "HPQ".
Qed.

Lemma staged_inv_alloc N k E E' P Q Qr:
  ▷ Q ∗ □ (C -∗ Q -∗ P ∗ Qr) ={E}=∗
  ∃ γ γ', staged_inv N k E' E' γ γ' P ∗ staged_value N γ Q Qr ∗ staged_pending γ'.
Proof.
  iMod (saved_prop_alloc Q) as (γprop) "#Hsaved".
  iMod (saved_prop_alloc Qr) as (γprop') "#Hsaved'".
  iMod (own_alloc (● (Excl' (γprop, γprop')) ⋅ ◯ (Excl' (γprop, γprop')))) as (γ) "[H1 H2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }
  iMod (own_alloc (Cinl (Excl ()))) as (γ') "H".
  { econstructor. }
  iIntros "(HQ&#HQP)".
  iMod (inv_alloc N E _ with "[HQ H1]") as "HI"; last first.
  { iModIntro. iExists γ, γ'. iFrame "H". iSplitL "HI".
    - iApply "HI".
    - iExists γprop, γprop'. iFrame. iFrame "#".
  }
  iNext. iExists γprop, γprop', Q, Qr. iFrame. iFrame "#".
  iAlways. iIntros. iApply step_fupdN_inner_later; auto; iNext.
  iApply "HQP"; by iFrame.
Qed.

Lemma staged_inv_open E N k E1 E2 γ γ' P Q Qr:
  ↑N ⊆ E →
  E2 ⊆ E1 →
  staged_inv N k E1 E2 γ γ' P ∗
  staged_value N γ Q Qr ={E,E∖↑N}=∗
  (▷ ▷ Q ∗ (∀ Q' Qr', ▷ Q' ∗ □ (C -∗ Q' -∗ |={E1, E2}_k=> P ∗ Qr') ={E∖↑N,E}=∗ staged_value N γ Q' Qr')) ∨
  (▷ ▷ Qr ∗ C ∗ |={E∖↑N, E}=> emp).
Proof.
  iIntros (??) "(#Hinv&Hval)".
  iDestruct "Hval" as (γprop γprop') "(Hγ&#Hsaved&#Hsaved')".
  iInv N as (γprop_alt γprop'_alt Qsaved Qrsaved) "H" "Hclose".
  iDestruct "H" as "(>Hγ'&#Hsaved_alt&#Hsaved'_alt&HQ0&Hcase)".
  iDestruct (own_valid_2 with "Hγ' Hγ") as "#H".
  iDestruct "H" as %[Heq%Excl_included%leibniz_equiv _]%auth_both_valid.
  inversion Heq; subst.
  iDestruct "Hcase" as "[HQ|Hdone]".
  {
    iModIntro. iLeft.
    iSplitL "HQ".
    - iModIntro.
      iDestruct (saved_prop_agree with "Hsaved Hsaved_alt") as "Hequiv".
      iNext. by iRewrite "Hequiv".
    - iIntros (Q' Qr'). iIntros "(HQ'&#HQ'impl)".
      iMod (saved_prop_alloc Q') as (γprop_new) "#Hsaved_new".
      iMod (saved_prop_alloc Qr') as (γprop'_new) "#Hsaved'_new".
      iMod (own_update_2 _ _ _ (● Excl' (γprop_new, γprop'_new) ⋅
                                ◯ Excl' (γprop_new, γprop'_new)) with "Hγ' Hγ") as "[Hγ' Hγ]".
      { by apply auth_update, option_local_update, exclusive_local_update. }
      iMod ("Hclose" with "[HQ' Hγ']").
      * iNext. iExists γprop_new, γprop'_new, _, _. iFrame "#". iFrame.
      * iModIntro. iExists γprop_new, γprop'_new. iFrame "#". iFrame.
  }
  {
    iDestruct "Hdone" as "(HQ&>#HC&>#Hdone)".
    iModIntro. iRight.
    iSplitL "HQ".
    - iModIntro.
      iDestruct (saved_prop_agree with "Hsaved' Hsaved'_alt") as "Hequiv".
      iNext. by iRewrite "Hequiv".
    - iFrame "HC".
      iMod (saved_prop_alloc P) as (γprop_new) "#Hsaved_new".
      iMod (saved_prop_alloc True) as (γprop'_new) "#Hsaved'_new".
      iMod (own_update_2 _ _ _ (● Excl' (γprop_new, γprop'_new) ⋅
                                ◯ Excl' (γprop_new, γprop'_new)) with "Hγ' Hγ") as "[Hγ' Hγ]".
      { by apply auth_update, option_local_update, exclusive_local_update. }
      iMod ("Hclose" with "[Hγ']").
      * iNext. iExists γprop_new, γprop'_new, _, _. iFrame "#". iFrame.
        iAlways. iIntros. iApply step_fupdN_inner_later; auto; iNext; by iFrame.
      * eauto.
  }
Qed.

Lemma staged_inv_weak_open E N k E1 γ γ' P:
  ↑N ⊆ E →
  E1 ⊆ E ∖ ↑N →
  staged_inv N k E1 E1 γ γ' P ∗
  staged_pending γ' ∗
  C -∗ |={E,E}_(S k)=> P.
Proof.
  iIntros (??) "(#Hinv&Hpending&#HC)".
  iInv N as (γprop_alt γprop'_alt Qsaved Qrsaved) "H" "Hclose".
  iDestruct "H" as "(>Hγ'&#Hsaved_alt&#Hsaved'_alt&#HQ0&Hcase)".
  iDestruct "Hcase" as "[HQ|Hfalse]"; last first.
  { iDestruct "Hfalse" as "(?&?&>H)".
    iDestruct (pending_done with "[$] [$]") as "[]".
  }
  iMod (fupd_intro_mask' _ E1) as "Hclo_E"; first auto.
  iMod (fupd_intro_mask' _ (∅)) as "Hclo_E1"; first by set_solver.
  iModIntro. rewrite Nat_iter_S. iModIntro. iNext.
  iMod "Hclo_E1" as "_".
  iMod ("HQ0" with "[$] [$]") as "H".
  iApply (step_fupdN_wand with "H"). iIntros "!> H".
  iMod "H" as "(HP&HQr)".
  iMod (pending_upd_done with "[$]") as "#Hdone".
  iMod "Hclo_E" as "_".
  iMod ("Hclose" with "[HQr Hγ']").
  { iNext. iExists _, _, _, _. iFrame "Hγ'". iFrame "#". by iRight. }
  iModIntro. eauto.
Qed.

(*
Global Instance into_inv_staged_inv1 N γ P : IntoInv (staged_inv N γ P) N := {}.

Definition staged_inv_exact N Pweak P :=
  (∃ γ, staged_inv N γ Pweak ∗ staged_value N γ P)%I.
*)

(*
Global Instance into_acc_inv E N γ Pweak P :
  IntoAcc (staged_inv_exact N γ Pweak P)
          (↑N ⊆ E) True (fupd E (E∖↑N)) (fupd (E∖↑N) E)
          (λ _, ▷ ▷ P)%I (λ Q, Q ∗ ▷ P)%I (λ Q, Some (staged_value N γ Q))%I.
Proof.
  rewrite /IntoAcc /accessor.
  iIntros (?) "(#Hinv&Hvalue) _". iMod (staged_inv_open with "[Hvalue]") as "($&?)"; first done.
  { by iFrame. }
  simpl default.
  { auto.

  i

                                                                 Apply inv_open; done.
Qed.

Lemma inv_open_timeless E N P `{!Timeless P} :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ P ∗ (P ={E∖↑N,E}=∗ True).
Proof.
  iIntros (?) "Hinv". iMod (inv_open with "Hinv") as "[>HP Hclose]"; auto.
  iIntros "!> {$HP} HP". iApply "Hclose"; auto.
Qed.
*)

End inv.
