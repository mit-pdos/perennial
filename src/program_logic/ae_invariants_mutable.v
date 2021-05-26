From stdpp Require Export namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap.
From Perennial.base_logic.lib Require Export fancy_updates fupd_level.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.base_logic.lib Require Import ae_invariants.
Set Default Proof Using "Type".
Import uPred.

(* TODO: work out semantic characterization ? *)

Definition ae_inv_mut_def `{!invGS Σ} (k: nat) mj sch (Ps : list (iProp Σ)) : iProp Σ :=
    ∃ i, ⌜i ∈ AE_next_diff (S k) mj⌝ ∧ ownI k i sch (list_to_vec Ps).
Definition ae_inv_mut_aux : seal (@ae_inv_mut_def). Proof. by eexists. Qed.
Definition ae_inv_mut {Σ i} := ae_inv_mut_aux.(unseal) Σ i.
Definition ae_inv_mut_eq : @ae_inv_mut = @ae_inv_mut_def := ae_inv_mut_aux.(seal_eq).
Instance: Params (@ae_inv_mut) 3 := {}.
Typeclasses Opaque ae_inv_mut.

Definition ae_inv_mut_full_def `{!invGS Σ} (k: nat) mj sch (Qs Ps : list (iProp Σ)) : iProp Σ :=
    ∃ i, ⌜i ∈ AE_next_diff (S k) mj ⌝ ∗ ownI k i sch (list_to_vec Ps) ∗ ownI_mut k i (1/2)%Qp (list_to_vec Qs).
Definition ae_inv_mut_full_aux : seal (@ae_inv_mut_full_def). Proof. by eexists. Qed.
Definition ae_inv_mut_full {Σ i} := ae_inv_mut_full_aux.(unseal) Σ i.
Definition ae_inv_mut_full_eq : @ae_inv_mut_full = @ae_inv_mut_full_def := ae_inv_mut_full_aux.(seal_eq).
Instance: Params (@ae_inv_mut_full) 3 := {}.
Typeclasses Opaque ae_inv_mut_full.

Local Hint Extern 0 (AE _ _ ## MaybeEn1 _) => apply AE_MaybeEn_disj : core.
Local Hint Extern 0 (AlwaysEn ## MaybeEn1 _) => apply coPset_inl_inr_disj : core.

Section ae_inv_mut.
  Context `{!invGS Σ}.
  Implicit Types i : positive.
  Implicit Types mj: option nat.
  Implicit Types E : coPset.
  Implicit Types P Q R : iProp Σ.
  Implicit Types Ps Qs Rs : list (iProp Σ).

  Definition ae_shift k mj E P P' Q :=
    (match mj with
     | None =>
       match k with
       | O => P ==∗ ◇ (P' ∗ Q)
       | S k' => P -∗ |k',(Some O)={E}=> P' ∗ Q
       end
     | Some j => P -∗ |k,(Some (S j))={E}=> P' ∗ Q
     end)%I.

  Lemma ae_inv_mut_full_acc k mj E sch Qs Qs' Ps R :
    ae_inv_mut_full k mj sch Qs Ps -∗
    ae_shift k mj E
             (bi_schema_interp k (bi_later <$> Ps) (bi_later <$> Qs) sch)
             (bi_schema_interp k (bi_later <$> Ps) (bi_later <$> Qs') sch)
             R -∗
    |k,mj={E}=> ae_inv_mut_full k mj sch Qs' Ps ∗ R.
  Proof.
    rewrite uPred_fupd_split_level_eq /uPred_fupd_split_level_def ae_inv_mut_full_eq.
    iDestruct 1 as (i) "[Hi [#HiP Hi_mut]]".
    iIntros "Hshift".
    iDestruct "Hi" as % ?%elem_of_subseteq_singleton.
    rewrite ?(ownE_op (AE _ _)) // ownE_AE_split_current_rest.
    rewrite {1 2}(union_difference_L {[ i ]} (AE_next_diff (S k) mj)) // ownE_op; last set_solver.
    iIntros "(Hw & ((Hi&HAE')&HAE) & HE)".
    iDestruct (ownI_open k i with "[$Hw $Hi $HiP]") as "(Hw & HI & HD)".
    iDestruct "HI" as (? Qs_mut) "(Hinterp&Hmut)".
    iDestruct (ownI_mut_agree with "Hi_mut Hmut") as (Hlen) "#Hequiv".
    iDestruct (bi_schema_interp_ctx_later with "[] Hequiv Hinterp") as "Hinterp".
    { iIntros. iNext. eauto. }
    rewrite ?vec_to_list_to_vec.

    destruct mj; last first.
    { destruct k.
      - iMod ("Hshift" with "[$]") as ">(HP&HR)".
        iFrame "HR HAE".
        iDestruct (ownI_mut_combine  with "[$] [$]") as "Hmut". rewrite Qp_div_2.
        iMod (ownI_close_modify O _ _ (list_to_vec Ps) (list_to_vec Qs')
                with "[$Hw $HiP $Hmut $HD HP]") as "($&HE'&Hmut)".
        { rewrite ?vec_to_list_to_vec. iFrame "HP". }
        rewrite ?(ownE_op (AE _)) //.
        iFrame "HAE' HE HE'".
        do 2 iModIntro. iExists _; iFrame "# ∗". iPureIntro; set_solver.
      - iDestruct (wsat_le_acc (S k) with "Hw") as "(Hw&Hclo)"; first lia.
        rewrite /ae_shift. rewrite uPred_fupd_split_level_eq /uPred_fupd_split_level_def.
        rewrite ownE_op //.
        iMod ("Hshift" with "Hinterp [$Hw $HAE $HE]") as ">(Hw&(HAE&HE)&HP&HR)".
        iFrame "HR HAE ".
        iDestruct (ownI_mut_combine  with "[$] [$]") as "Hmut". rewrite Qp_div_2.
        iDestruct ("Hclo" with "[$]") as "Hw".
        iMod (ownI_close_modify (S k) _ _ (list_to_vec Ps) (list_to_vec Qs')
                with "[$Hw $HiP $Hmut $HD HP]") as "($&HE'&Hmut)".
        { rewrite ?vec_to_list_to_vec. iFrame "HP". }
        rewrite ?(ownE_op (AE _)) //.
        iFrame "HAE' HE HE'".
        do 2 iModIntro. iExists _; iFrame "# ∗". iPureIntro; set_solver.
    }
    - rewrite /ae_shift. rewrite uPred_fupd_split_level_eq /uPred_fupd_split_level_def.
      rewrite ownE_op //.
      iMod ("Hshift" with "Hinterp [$Hw $HAE $HE]") as ">(Hw&(HAE&HE)&HP&HR)".
      iFrame "HR HAE ".
      iDestruct (ownI_mut_combine  with "[$] [$]") as "Hmut". rewrite Qp_div_2.
      iMod (ownI_close_modify k _ _ (list_to_vec Ps) (list_to_vec Qs')
              with "[$Hw $HiP $Hmut $HD HP]") as "($&HE'&Hmut)".
      { rewrite ?vec_to_list_to_vec. iFrame. }
      rewrite ?(ownE_op (AE _)) //.
      iFrame "HAE' HE HE'".
      do 2 iModIntro. iExists _; iFrame "# ∗". iPureIntro; set_solver.
  Qed.

  Lemma ae_inv_mut_acc k mj E sch Ps R :
    ae_inv_mut k mj sch Ps -∗
    (∀ Qs, ae_shift k mj E
             (bi_schema_interp k (bi_later <$> Ps) (bi_later <$> Qs) sch)
             (bi_schema_interp k (bi_later <$> Ps) (bi_later <$> Qs) sch)
             R) -∗
    |k,mj={E}=> R.
  Proof.
    rewrite uPred_fupd_split_level_eq /uPred_fupd_split_level_def ae_inv_mut_eq.
    iDestruct 1 as (i) "[Hi #Hinv]".
    iIntros "Hshift".
    iDestruct "Hi" as % ?%elem_of_subseteq_singleton.
    rewrite ?(ownE_op (AE _ _)) // ownE_AE_split_current_rest.
    rewrite {1 2}(union_difference_L {[ i ]} (AE_next_diff (S k) mj)) // ownE_op; last set_solver.
    iIntros "(Hw & ((Hi&HAE')&HAE) & HE)".
    iDestruct (ownI_open k i with "[$Hw $Hi $Hinv]") as "(Hw & HI & HD)".
    iDestruct "HI" as (? Qs_mut) "(Hinterp&Hmut)".
    rewrite ?vec_to_list_to_vec.

    destruct mj; last first.
    { destruct k.
      - iMod ("Hshift" with "[$]") as ">(HP&HR)".
        iFrame "HR HAE".
        iDestruct (ownI_close O _ _ (list_to_vec Ps) with "[$Hw $Hinv $Hmut $HD HP]") as "H".
        { rewrite ?vec_to_list_to_vec. iFrame "HP". }
        iFrame. eauto.
      - iDestruct (wsat_le_acc (S k) with "Hw") as "(Hw&Hclo)"; first lia.
        rewrite /ae_shift. rewrite uPred_fupd_split_level_eq /uPred_fupd_split_level_def.
        iSpecialize ("Hshift" $! _).
        rewrite ownE_op //.
        iMod ("Hshift" with "Hinterp [$Hw $HAE $HE]") as ">(Hw&(HAE&HE)&HP&HR)".
        iFrame "HR HAE ".
        iDestruct ("Hclo" with "[$]") as "Hw".
        iDestruct (ownI_close _ _ _ (list_to_vec Ps) with "[$Hw $Hinv $Hmut $HD HP]") as "H".
        { rewrite ?vec_to_list_to_vec. iFrame "HP". }
        iFrame. eauto.
    }
    - rewrite /ae_shift. rewrite uPred_fupd_split_level_eq /uPred_fupd_split_level_def.
      iSpecialize ("Hshift" $! _).
      rewrite ownE_op //.
      iMod ("Hshift" with "Hinterp [$Hw $HAE $HE]") as ">(Hw&(HAE&HE)&HP&HR)".
      iFrame "HR HAE ".
      iDestruct (ownI_close _ _ _ (list_to_vec Ps) with "[$Hw $Hinv $Hmut $HD HP]") as "H".
      { rewrite ?vec_to_list_to_vec. iFrame "HP". }
      iFrame. eauto.
  Qed.

  Lemma ae_inv_mut_alloc k mj E sch Ps Qs :
    bi_schema_interp k (bi_later <$> Ps) (bi_later <$> Qs) sch -∗
    |k,mj={E}=> ae_inv_mut k mj sch Ps ∗ ae_inv_mut_full k mj sch Qs Ps.
  Proof.
    rewrite uPred_fupd_split_level_eq ?ae_inv_mut_eq ?ae_inv_mut_full_eq. iIntros "HP [Hw $]".
    iMod (ownI_alloc (.∈ AE_next_diff (S k) mj) sch k (list_to_vec Ps) (list_to_vec Qs)
            with "[HP $Hw]")
      as (i ?) "[$ [#HI ?]]"; auto using fresh_ae_inv_name.
    { by rewrite ?vec_to_list_to_vec. }
    do 2 iModIntro. iSplitL ""; iExists _; iFrame "# ∗"; eauto.
  Qed.

  Global Instance ae_inv_mut_persistent k sch mj Ps : Persistent (ae_inv_mut k mj sch Ps).
  Proof. rewrite ae_inv_mut_eq. apply _. Qed.

  (** ** Proof mode integration *)
  (* TODO *)
  (*
  Global Instance into_inv_inv N P : IntoInv (inv N P) N := {}.

  Global Instance into_acc_inv_lvl k N P E:
    IntoAcc (X := unit) (inv N P)
            (↑N ⊆ E) True (uPred_fupd_level E (E ∖ ↑N) k) (uPred_fupd_level (E ∖ ↑N) E k)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite inv_eq /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hinv _". iApply (fupd_level_le _ _ O); first lia.
    iMod ("Hinv" $! _ with "[//]") as "($&Hcl)".
    iModIntro. iIntros "H". iSpecialize ("Hcl" with "H").
    iApply (fupd_level_le with "Hcl"); first lia.
  Qed.

  Global Instance into_acc_inv N P E:
    IntoAcc (X := unit) (inv N P)
            (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite inv_eq /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hinv _". iApply (fupd_level_fupd _ _ _ O).
    iMod ("Hinv" $! _ with "[//]") as "($&Hcl)".
    iModIntro. iIntros "H". iSpecialize ("Hcl" with "H").
    iApply (fupd_level_fupd with "Hcl").
  Qed.
   *)

End ae_inv_mut.
