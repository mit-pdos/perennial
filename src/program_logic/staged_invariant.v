From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From iris.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From iris.base_logic.lib Require Import wsat invariants ae_invariants saved_prop.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export step_fupd_extra crash_weakestpre ae_invariants_mutable.
Set Default Proof Using "Type".
Import uPred.

Class stagedG (Σ : gFunctors) : Set := WsatG {
  staging_shot_inG :> inG Σ (csumR (fracR) (agreeR unitO));
}.

Definition stagedΣ : gFunctors :=
    #[GFunctor (csumR fracR (agreeR unitO))].

Instance subG_stagedG {Σ} : subG stagedΣ Σ → stagedG Σ.
Proof. solve_inG. Qed.

Definition staged_pending `{stagedG Σ} (q: Qp) (γ: gname) : iProp Σ :=
  own γ (Cinl q).
Definition staged_done `{stagedG Σ} (γ: gname) : iProp Σ :=
  own γ (Cinr (to_agree ())).

(* Schema:
   Fixed: O => C, 1 => P
   Mutable: O => Qs *)

Definition bi_sch_cfupd E E' P :=
  bi_sch_wand (bi_sch_var_fixed O) (bi_sch_fupd E E (bi_sch_fupd E' ∅ P)).

Definition bi_sch_staged_fupd (E: coPset) :=
  bi_sch_persistently
    (bi_sch_wand (bi_sch_var_mut O)
                 (bi_sch_wand (bi_sch_var_fixed 2)
                    (bi_sch_cfupd E ∅ (bi_sch_sep (bi_sch_var_fixed 1) (bi_sch_var_mut O))))).

Definition bi_sch_staged_cases :=
  bi_sch_or (bi_sch_var_mut O)
            (bi_sch_sep (bi_sch_var_mut 1) (bi_sch_sep (bi_sch_var_fixed O) (bi_sch_var_fixed 1))).

Definition bi_sch_staged E :=
  bi_sch_and (bi_sch_var_mut O) (bi_sch_staged_fupd E).

(* XXX: unfortunately this lemma swaps the ▷ C and the staged_pending 1%Qp γ from the way
   the schema is structured, but to not break other proofs, we swap the order here *)
Lemma bi_sch_staged_interp `{!invG Σ, !crashG Σ, !stagedG Σ} E k Qs P γ :
  bi_schema_interp (S k) (bi_later <$> [C; P; staged_pending 1%Qp γ])
                   (bi_later <$> [Qs]) (bi_sch_staged E)
  ⊣⊢ ((▷ Qs ∧ □ (▷ Qs -∗ ▷ C -∗ staged_pending 1%Qp γ -∗ |k,Some O={E}=> |k, Some O={∅, ∅}=> ▷ P ∗ ▷ Qs)))%I.
Proof.
  rewrite bi_schema_interp_unfold.
  rewrite /bi_sch_staged.
  rewrite bi_schema_interp_unfold.
  rewrite /bi_sch_staged_fupd.
  rewrite bi_schema_interp_unfold.
  rewrite bi_schema_interp_unfold.
  rewrite list_lookup_fmap. simpl ([Qs] !! 0).
  rewrite bi_schema_interp_unfold.
  rewrite /bi_sch_cfupd.
  rewrite bi_schema_interp_unfold.
  rewrite bi_schema_interp_unfold.
  rewrite bi_schema_interp_unfold.
  erewrite bi_sch_fupd_interp; last first.
  { erewrite bi_sch_fupd_interp; last first.
    { rewrite //=. }
    reflexivity. }
  rewrite //=.
  f_equiv.
  rewrite intuitionistically_into_persistently.
  f_equiv. f_equiv.
  rewrite wand_curry.
  rewrite wand_curry.
  rewrite sep_comm.
  rewrite -wand_curry.
  rewrite -wand_curry.
  f_equiv.
  iSplit.
   - iIntros "H1 H2". iApply "H1". eauto.
   - iIntros "H1 >H2". iApply "H1". eauto.
Qed.

Lemma bi_sch_staged_interp_weak `{!invG Σ, !crashG Σ, !stagedG Σ} E k Qs_mut P γ :
  bi_schema_interp (S k) (bi_later <$> [C; P; staged_pending 1%Qp γ]) (bi_later <$> Qs_mut) (bi_sch_staged E)
                   ⊣⊢ let Qs := default emp%I (bi_later <$> (Qs_mut !! O)) in
                      (((Qs ∧ □ (Qs -∗ ▷ C -∗ staged_pending 1%Qp γ -∗ |k,Some O={E}=> |k, Some O={∅, ∅}=> ▷ P ∗ Qs))))%I.
Proof.
  rewrite bi_schema_interp_unfold.
  rewrite /bi_sch_staged.
  rewrite bi_schema_interp_unfold.
  rewrite /bi_sch_staged_fupd.
  rewrite bi_schema_interp_unfold.
  rewrite bi_schema_interp_unfold.
  rewrite bi_schema_interp_unfold.
  rewrite /bi_sch_cfupd.
  rewrite bi_schema_interp_unfold.
  rewrite bi_schema_interp_unfold.
  rewrite bi_schema_interp_unfold.
  erewrite bi_sch_fupd_interp; last first.
  { erewrite bi_sch_fupd_interp; last first.
    { rewrite //=. }
    reflexivity. }
  rewrite //=.
  f_equiv.
  { rewrite ?list_lookup_fmap. destruct (Qs_mut !! 0) => //=. }
  rewrite intuitionistically_into_persistently.
  f_equiv. f_equiv.
  { rewrite ?list_lookup_fmap. destruct (Qs_mut !! 0) => //=. }
  rewrite wand_curry.
  rewrite wand_curry.
  rewrite sep_comm.
  rewrite -wand_curry.
  rewrite -wand_curry.
  f_equiv.
  iSplit.
  - iIntros "H1 H2".
    rewrite ?list_lookup_fmap. destruct (Qs_mut !! 0) => //=; iApply "H1"; eauto.
  - iIntros "H1 >H2".
    rewrite ?list_lookup_fmap. destruct (Qs_mut !! 0) => //=; iApply "H1"; eauto.
Qed.

Section staged_inv_defns.

  Context `{!invG Σ, !crashG Σ, !stagedG Σ}.

Definition staged_inv (k: nat) E (γ: gname) (P: iProp Σ) : iProp Σ :=
  ae_inv_mut k None (bi_sch_staged E) [C; P; staged_pending 1%Qp γ].

Definition staged_value (k: nat) k2 mj2  E (γp: gname) (Qs Qr P: iProp Σ) :=
  (∃ γcancel γr,
  staged_pending 1%Qp γr ∗
  staged_pending (1/2)%Qp γcancel ∗
  ae_inv k2 (Some mj2) ((Qs ∨ ((Qr ∨ staged_done γr) ∗ C ∗ (P ∨ staged_done γp))) ∨ staged_done γcancel) ∗
  ae_inv_mut_full k None (bi_sch_staged E) [staged_pending (1/2)%Qp γcancel] [C; P; staged_pending 1%Qp γp])%I.

Definition staged_value_disc (k: nat) (mj: nat) (γp: gname) (Qs Qr P: iProp Σ) :=
  (∃ γcancel γr,
  staged_pending 1%Qp γr ∗
  staged_pending (1/2)%Qp γcancel ∗
  ae_inv k (Some mj) ((Qs ∨ ((Qr ∨ staged_done γr) ∗ C ∗ (P ∨ staged_done γp))) ∨ staged_done γcancel))%I.

End staged_inv_defns.

Section inv.
Context `{!invG Σ, !stagedG Σ, !crashG Σ}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Σ.

(*
Global Instance staged_contractive k N E E' γ : Contractive (staged_inv k N E E' γ).
Proof.
  rewrite /staged_inv=> n ?? ?.
  repeat (apply step_fupdN_ne || f_contractive || f_equiv); eauto.
Qed.

Global Instance staged_ne N E E' γ γ': NonExpansive (staged_inv N E E' γ γ').
Proof.
  rewrite /staged_inv=> n ?? ?.
  repeat (apply step_fupdN_ne || f_contractive || f_equiv); eauto using dist_le.
Qed.

Global Instance staged_proper N E E' γ γ' : Proper ((⊣⊢) ==> (⊣⊢)) (staged_inv N E E' γ γ').
Proof. apply ne_proper, _. Qed.
*)

Global Instance staged_persistent k E γ P : Persistent (staged_inv k E γ P).
Proof. rewrite /staged_inv. apply _. Qed.

Lemma pending_done q γ: staged_pending q γ -∗ staged_done γ -∗ False.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

Lemma pending_upd_done γ: staged_pending 1%Qp γ ==∗ staged_done γ.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H". iMod (own_update with "H") as "$".
  { by apply cmra_update_exclusive. }
  done.
Qed.

Lemma pending_alloc:
  ⊢ |==> ∃ γ, staged_pending 1 γ.
Proof.
  iApply (own_alloc (Cinl 1%Qp)).
  { rewrite //=. }
Qed.

Lemma pending_split γ:
  staged_pending 1 γ ⊢ staged_pending (1/2)%Qp γ ∗ staged_pending (1/2)%Qp γ.
Proof. by rewrite /staged_pending -own_op -Cinl_op frac_op' Qp_div_2. Qed.

Lemma pending_join γ:
 staged_pending (1/2)%Qp γ ∗ staged_pending (1/2)%Qp γ ⊢  staged_pending 1 γ.
Proof. by rewrite /staged_pending -own_op -Cinl_op frac_op' Qp_div_2. Qed.

Lemma staged_inv_alloc k E E' P Q Qr:
  ▷ Q ∗ □ (C -∗ ▷ Q -∗ ▷ P ∗ ▷ Qr) -∗ |(S k)={E}=>
  ∃ γ, staged_inv (S k) E' γ P ∗ staged_value (S k) O O E' γ Q Qr P ∗ staged_pending 1%Qp γ.
Proof.
  iMod (pending_alloc) as (γp) "Hp".
  iMod (pending_alloc) as (γcancel) "Hc".
  iMod (pending_alloc) as (γr) "Hr".
  iIntros "(HQ&HQP)".
  rewrite uPred_fupd_level_eq.
  iPoseProof (ae_inv_alloc' O (Some O) E
        (((Q ∨ ((Qr ∨ staged_done γr) ∗ C ∗ (P ∨ staged_done γp))) ∨ staged_done γcancel))%I
        with "[HQ]") as "H".
  { repeat iLeft. auto. }
  iDestruct (pending_split with "Hc") as "(Hc1&Hc2)".
  iMod (fupd_split_level_le with "H") as "#Hinv0".
  { lia. }

  iMod (ae_inv_mut_alloc (S k) None E (bi_sch_staged E')
                         [C; P; staged_pending 1%Qp γp]
                         [staged_pending (1/2)%Qp γcancel]
          with "[Hc1 HQP]")
    as "(#Hi&Hmut)".
  { simpl fmap. rewrite bi_sch_staged_interp.
    iSplit; first iFrame.
    iDestruct "HQP" as "#HQP". iModIntro.
    iIntros ">Hc1 >#HC Hpend".
    iPoseProof (ae_inv_acc E' _ _ _ (▷ P ∗ staged_pending (1/2) γcancel) with "Hinv0 [Hc1 HQP Hpend]") as "H".
    { iIntros "[HQ|>Hfalse]"; last first.
      { iDestruct (pending_done with "Hc1 [$]") as %[]. }
      iDestruct "HQ" as "[HQ|H]".
      { iDestruct ("HQP" with "[$] [$]") as "($&HQr)".
        iMod (pending_upd_done with "Hpend") as "#Hdone".
        iModIntro. iFrame "Hc1". iLeft. iRight. iFrame "# ∗".
      }
      iDestruct "H" as "(HQ&_&[HP|>Hfalse])"; last first.
      { iDestruct (pending_done with "Hpend [$]") as %[]. }
      iMod (pending_upd_done with "Hpend") as "#Hdone".
      iModIntro. iFrame "Hc1". iFrame "HP". iLeft. iFrame "# ∗".
    }
    iMod (fupd_split_level_le with "H") as "(?&?)"; first (naive_solver lia).
    iFrame. eauto.
  }
  iModIntro. iExists _. iFrame "# ∗". iExists _, _. iFrame "# ∗".
Qed.

Lemma staged_inv_open_modify_ae E k k2 k2' j j' E1 γ P Q Qr Q' Qr' R:
  k2 ≤ k →
  k2' ≤ k →
  staged_value (S k) k2 j E1 γ Q Qr P -∗
  (▷ Q -∗ |k,Some O={E}=> □ (▷ Q' -∗ C -∗ |k2',Some (S j')={E1}=> |k2',Some (S j')={∅, ∅}=> ▷ P ∗ ▷ Qr') ∗  ▷ Q' ∗ R) -∗
  |(S k)={E}=> (R ∗ staged_value (S k) k2' j' E1 γ Q' Qr' P) ∨
               (▷ Qr ∗ C).
Proof.
  iIntros (Hle Hle') "Hval Hshift".
  rewrite /staged_value/=.
  iMod (pending_alloc) as (γcancel') "Hc".
  iDestruct (pending_split with "Hc") as "(Hc1&Hc2)".
  iDestruct "Hval" as (γcancel γr) "(Hγr&Hcancel&#Hinv0&Hval)" => //=.
  iEval (rewrite uPred_fupd_level_eq).
  iMod (ae_inv_mut_full_acc _ _ _ _ _ ([staged_pending (1/2)%Qp γcancel']) _
                            (((R ∗ staged_pending 1%Qp γr ∗
                                 ae_inv k2' (Some j') ((Q' ∨ (Qr' ∨ staged_done γr) ∗ C ∗ (P ∨ staged_done γ))
                                                         ∨ staged_done γcancel')))
                             ∨
                            (((▷ Qr ∗ staged_done γr ∗ C))))%I
          with "Hval [Hcancel Hγr Hshift Hc1]") as "(HR&Hclo)";
    last first.
  { iModIntro. iDestruct "Hclo" as "[(Hr&?&#Hinv)|(?&?&?)]".
    - iLeft. iFrame. iExists _, _. iFrame; eauto.
    - iRight. iFrame.
  }
  iIntros "HQ".
  iDestruct (bi_sch_staged_interp with "HQ") as "HQ".
  iDestruct "HQ" as "(>Hcancel'&_)".

  (* Cancel the old invariant *)
  iDestruct (pending_join with "[$Hcancel $Hcancel']") as "Hcancel".
  iPoseProof (ae_inv_acc E _ _ _ (▷ (Q ∨ (Qr ∨ staged_done γr) ∗ C ∗ (P ∨ staged_done γ)))
                with "Hinv0 [Hcancel]") as "H".
  { iIntros "[Hleft|>Hfalse]".
    { iMod (pending_upd_done with "Hcancel"). iModIntro. iSplitR "Hleft"; last by iFrame.
      iFrame "∗". }
    iDestruct (pending_done with "[$] [$]") as %[].
  }
  iClear "Hinv0".
  iMod (fupd_split_level_le with "H") as "H".
  { naive_solver lia. }
  iDestruct "H" as "[HQ|HQ]".
  - iMod ("Hshift" with "[$]") as "(Hwand&HQ'&HR)".
    iPoseProof (ae_inv_alloc' k2' (Some j') E
        (((Q' ∨ ((Qr' ∨ staged_done γr) ∗ C ∗ (P ∨ staged_done γ))) ∨ staged_done γcancel'))%I
        with "[HQ']") as "H".
    { repeat iLeft. auto. }
    iMod (fupd_split_level_le with "H") as "#Hinv".
    { naive_solver lia. }
    iModIntro.
    rewrite bi_sch_staged_interp. iFrame "Hinv".
    iSplitR "HR Hγr"; last first.
    { iLeft. by iFrame. }
    iSplit; first iFrame.
    iDestruct "Hwand" as "#Hwand".
    iModIntro. iIntros ">Hc1 >#HC Hpend".

    iPoseProof (ae_inv_acc E1 _ _ _ (▷ P ∗ staged_pending (1/2) γcancel') with "Hinv [Hc1 Hpend Hwand]") as "H".
    { iIntros "HQ".
      iDestruct "HQ" as "[HQ|>Hfalse]"; last first.
      { iDestruct (pending_done with "Hc1 Hfalse") as %[]. }
      iDestruct "HQ" as "[HQ|HQ]".
      * iMod ("Hwand" with "[$] [$]") as "H".
        iMod (fupd_split_level_intro_mask' _ ∅) as "Hclo''"; first by set_solver+.
        iMod ("H") as "(HP&HQr')".
        iMod (pending_upd_done with "Hpend").
        iMod "Hclo''" as "_".
        iModIntro. iFrame "Hc1 HP". iNext. iFrame "HC". iLeft.
        iRight. iFrame.
      * iDestruct "HQ" as "(HQr&_&[HP|>Hfalse])"; last first.
        { iDestruct (pending_done with "Hpend Hfalse") as %[]. }
        iMod (pending_upd_done with "Hpend").
        iModIntro. iFrame "Hc1 HP". iNext. iFrame "HC". iLeft.
        iRight. iFrame.
    }
    iMod (fupd_split_level_le with "H") as "(?&?)"; first (naive_solver lia).
    do 2 iModIntro; eauto. iFrame.
  - iDestruct "HQ" as "([HQr|>Hfalse]&#>HC&HP)"; last first.
    { iDestruct (pending_done with "Hγr Hfalse") as %[]. }
    iMod (pending_upd_done with "Hγr") as "#Hγr".
    iPoseProof (ae_inv_alloc' k2' (Some j') E
        (((((Qr' ∨ staged_done γr) ∗ C ∗ (P ∨ staged_done γ))) ∨ staged_done γcancel'))%I
        with "[Hγr HP]") as "H".
    { iLeft. iFrame. eauto. }
    iMod (fupd_split_level_le with "H") as "#Hinv".
    { naive_solver lia. }
    iModIntro.
    rewrite bi_sch_staged_interp.
    iSplitR "HQr Hγr"; last first.
    { iRight. iFrame "# ∗". }
    iSplit; first iFrame.
    iModIntro.
    iIntros ">Hc1 _ Hpend".
    iPoseProof (ae_inv_acc E1 _ _ _ (▷ P ∗ staged_pending (1/2) γcancel') with "Hinv [Hc1 Hpend]") as "H".
    { iIntros "HQ".
      iDestruct "HQ" as "[HQ|>Hfalse]"; last first.
      { iDestruct (pending_done with "Hc1 Hfalse") as %[]. }
      iDestruct "HQ" as "(HQr&_&[HP|>Hfalse])"; last first.
      { iDestruct (pending_done with "Hpend Hfalse") as %[]. }
      iMod (pending_upd_done with "Hpend").
      iModIntro. iFrame "Hc1 HP". iNext. iFrame "HC". iLeft.
      iFrame.
    }
    iMod (fupd_split_level_le with "H") as "(?&?)"; first (naive_solver lia).
    do 2 iModIntro; by iFrame.
Qed.

Lemma staged_value_into_disc k k2 mj2 E γ P Q Qr :
  staged_value k k2 mj2 E γ Q Qr P -∗
  <disc> staged_value_disc k2 mj2 γ Q Qr P.
Proof.
  iDestruct 1 as (??) "(Hp1&Hp2&#Hinv&_)".
  iModIntro. iExists _, _. by iFrame.
Qed.

Lemma staged_inv_disc_open_crash k mj E γ P Q Qr:
  □ (▷ Q -∗ ▷ C -∗ |k, Some (S mj)={E}=> |k, Some (S mj)={∅, ∅}=> ▷ P ∗ ▷ Qr) -∗
  staged_value_disc k mj γ Q Qr P -∗ C -∗ |k, Some mj={E}=> ▷ Qr.
Proof.
  iIntros "#Hwand".
  iDestruct 1 as (??) "(Hqr&Hqc&#Hinv)".
  iIntros "#HC".
  iMod (ae_inv_acc _ _ _ _ (▷ Qr)%I
          with "Hinv [Hqr Hqc]") as "$"; last done.
  iIntros "HQ".
  iDestruct "HQ" as "[HQ|>Hfalse]"; last first.
  { iDestruct (pending_done with "[$] [$]") as %[]. }
  iDestruct "HQ" as "[HQ|HQ]".
  - iMod ("Hwand" with "[$] [$]") as "H".
    iMod (fupd_split_level_intro_mask' _ ∅) as "Hclo''"; first by set_solver+.
    iMod ("H") as "(HP&HQr)".
    iMod "Hclo''" as "_".
    iMod (pending_upd_done with "Hqr") as "#Hdone".
    iModIntro. iFrame "HQr". iLeft. iRight. iFrame "# ∗".
  - iDestruct "HQ" as "([HQr|>Hfalse]&_&HP)"; last first.
    { iDestruct (pending_done with "Hqr [$]") as %[]. }
    iMod (pending_upd_done with "Hqr") as "#Hdone".
    iModIntro. iFrame "HQr".
    iLeft. iRight. iFrame "# ∗".
Qed.

Lemma staged_inv_weak_open E k E1 γ P:
  E1 ⊆ E →
  staged_inv (S k) E1 γ P ∗
  staged_pending 1%Qp γ ∗
  C -∗ |(S k)={E,E}=> ▷ P.
Proof.
  iIntros (?) "(#Hinv&Hpending&#HC)".
  rewrite /staged_inv.
  rewrite uPred_fupd_level_eq.
  iMod (ae_inv_mut_acc _ _ _ _ _ (▷ P) with "Hinv [Hpending]"); last done.
  iIntros (Qs) "Hinv0".
  iDestruct (bi_sch_staged_interp_weak with "Hinv0") as "H".
  iDestruct "H" as "(Hc&#Hwand)".
  iMod (fupd_split_level_intro_mask' _ E1) as "Hclo''"; auto.
  iDestruct ("Hwand" with "[$] [$] [$]") as "Hwand0".
  iMod (fupd_split_level_le with "Hwand0") as "Hwand0"; first (naive_solver lia).
  iMod (fupd_split_level_intro_mask' _ ∅) as "Hclo'''"; first by set_solver.
  iMod (fupd_split_level_le with "Hwand0") as "(HP&HQr)"; first (naive_solver lia).
  iMod "Hclo'''" as "_".
  iMod "Hclo''" as "_".
  iModIntro. iSplitR "HP"; last done.
  iApply bi_sch_staged_interp_weak. iFrame "# ∗".
Qed.

End inv.
