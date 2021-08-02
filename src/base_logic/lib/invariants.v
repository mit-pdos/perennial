From stdpp Require Export namespaces.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.base_logic.lib Require Export fancy_updates fupd_level.
From Perennial.base_logic.lib Require Import wsat.
From iris.prelude Require Import options.
Import uPred.

(** Semantic Invariants *)
Definition inv_def `{!invGS Σ} (N : namespace) (P : iProp Σ) : iProp Σ :=
  □ ∀ E, ⌜↑N ⊆ E⌝ → |0={E,E ∖ ↑N}=> ▷ P ∗ (▷ P -∗ |0={E ∖ ↑N,E}=> True).
Definition inv_aux : seal (@inv_def). Proof. by eexists. Qed.
Definition inv := inv_aux.(unseal).
Global Arguments inv {Σ _} N P.
Definition inv_eq : @inv = @inv_def := inv_aux.(seal_eq).
Global Instance: Params (@inv) 3 := {}.

Local Hint Extern 0 (AE _ _ ## MaybeEn1 _) => apply AE_MaybeEn_disj : core.
Local Hint Extern 0 (AlwaysEn ## MaybeEn1 _) => apply coPset_inl_inr_disj : core.

(** * Invariants *)
Section inv.
  Context `{!invGS Σ}.
  Implicit Types i : positive.
  Implicit Types N : namespace.
  Implicit Types E : coPset.
  Implicit Types P Q R : iProp Σ.

  (** ** Internal model of invariants *)
  Definition own_inv (N : namespace) (P : iProp Σ) : iProp Σ :=
    ∃ i, ⌜i ∈ MaybeEn1 (↑N:coPset)⌝ ∧ ownI O i (bi_sch_var_fixed O) (list_to_vec [P]).

  Lemma own_inv_acc0 E N P :
    ↑N ⊆ E → own_inv N P -∗ |0={E,E∖↑N}=> ▷ P ∗ (▷ P -∗ |O={E∖↑N,E}=> True).
  Proof.
    rewrite uPred_fupd_level_eq /uPred_fupd_level_def.
    rewrite uPred_fupd_split_level_eq /uPred_fupd_split_level_def.
    iDestruct 1 as (i) "[Hi #HiP]".
    iDestruct "Hi" as % ?%elem_of_subseteq_singleton.
    rewrite ?(ownE_op (AE _ _)) //.
    rewrite {1 4}(union_difference_L (↑ N) E) // ownE_op_MaybeEn; last set_solver.
    rewrite {1 2}(union_difference_L {[ i ]} (MaybeEn1 (↑ N))) // ownE_op; last set_solver.
    iIntros "(Hw & HAE & [HE $] & $) !> !>".
    iDestruct (ownI_open O i with "[$Hw $HE $HiP]") as "($ & HI & HD)".
    iDestruct "HI" as (? Ps_mut) "(Hinterp&Hmut)".
    iEval (rewrite ?bi_schema_interp_unfold /=) in "Hinterp". iFrame "Hinterp".
    iFrame "HAE".
    iIntros "HP [Hw [$ $]] !> !>". iApply (ownI_close O _ _ (list_to_vec [P])). iFrame "# ∗".
  Qed.

  Lemma own_inv_acc E N P :
    ↑N ⊆ E → own_inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "Hown". iApply (fupd_level_fupd E _ _ O).
    iMod (own_inv_acc0 E N with "Hown") as "($&Hcl)"; first auto.
    iModIntro. iIntros "H". iSpecialize ("Hcl" with "H"). by iApply fupd_level_fupd.
  Qed.

  Lemma fresh_inv_name (E : gset positive) N : ∃ i, i ∉ E ∧ i ∈ MaybeEn1 (↑N:coPset).
  Proof.
    exists (coPpick (MaybeEn1 (↑ N) ∖gset_to_coPset E)).
    rewrite -elem_of_gset_to_coPset (comm and) -elem_of_difference.
    apply coPpick_elem_of=> Hfin.
    eapply (MaybeEn_infinite _ (nclose_infinite N)), (difference_finite_inv _ _), Hfin.
    apply gset_to_coPset_finite.
  Qed.

  Lemma own_inv_alloc0 N E P : ▷ P -∗ |0={E}=> own_inv N P.
  Proof.
    rewrite uPred_fupd_level_eq /uPred_fupd_level_def.
    rewrite uPred_fupd_split_level_eq /uPred_fupd_split_level_def.
    iIntros "HP [Hw $]".
    iMod (ownI_alloc (.∈ MaybeEn1 (↑N : coPset)) (bi_sch_var_fixed O) O (list_to_vec [P]) (list_to_vec [])
            with "[$HP $Hw]")
      as (i ?) "[$ [? ?]]"; auto using fresh_inv_name.
    do 2 iModIntro. iExists i. auto.
  Qed.

  Lemma own_inv_alloc N E P : ▷ P ={E}=∗ own_inv N P.
  Proof. iIntros "HP". iApply (fupd_level_fupd). by iApply own_inv_alloc0. Qed.

  (* This does not imply [own_inv_alloc] due to the extra assumption [↑N ⊆ E]. *)
  Lemma own_inv_alloc_open0 N E P :
    ↑N ⊆ E → ⊢ |0={E, E∖↑N}=> own_inv N P ∗ (▷P -∗ |0={E∖↑N, E}=> True).
  Proof.
    rewrite uPred_fupd_level_eq /uPred_fupd_level_def.
    rewrite uPred_fupd_split_level_eq /uPred_fupd_split_level_def.
    iIntros (Sub) "[Hw HE]".
    iMod (ownI_alloc_open O (.∈ MaybeEn1 (↑N : coPset)) (bi_sch_var_fixed O) (list_to_vec [P]) (list_to_vec [])
            with "Hw")
      as (i ?) "(Hw & #Hi & HD)"; auto using fresh_inv_name.
    iEval (rewrite ownE_op //) in "HE". iDestruct "HE" as "(HAE&HE)".
    assert (MaybeEn1 (↑N) ## MaybeEn1 (E ∖ ↑N)).
    { rewrite -MaybeEn_disj. set_solver. }
    iAssert (ownE {[i]} ∗ ownE (MaybeEn1 (↑ N) ∖ {[i]}) ∗ ownE (MaybeEn1 (E ∖ ↑ N)))%I
      with "[HE]" as "(HEi & HEN\i & HE\N)".
    { rewrite -?ownE_op; [| set_solver..].
      rewrite assoc_L -!union_difference_L //; last set_solver.
      rewrite -MaybeEn_union -!union_difference_L //.
    }
    do 2 iModIntro. rewrite ownE_op //. iFrame "HAE HE\N". iSplitL "Hw HEi"; first by iApply "Hw".
    iSplitL "Hi".
    { iExists i. auto. }
    iIntros "HP [Hw HE\N]".
    rewrite ?ownE_op //.
    iDestruct "HE\N" as "($&HE\N)".
    iDestruct (ownI_close with "[$Hw $Hi $HP $HD]") as "[$ HEi]".
    do 2 iModIntro.
    iCombine "HEi HEN\i HE\N" as "HEN".
    rewrite -?ownE_op; [|set_solver..].
    rewrite assoc_L -!union_difference_L //; last set_solver.
    rewrite -MaybeEn_union -!union_difference_L //.
  Qed.

  Lemma own_inv_alloc_open N E P :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> own_inv N P ∗ (▷P ={E∖↑N, E}=∗ True).
  Proof.
    iIntros (?). iApply (fupd_level_fupd E _ _ O).
    iMod (own_inv_alloc_open0 N) as "($&Hcl)"; first auto.
    iModIntro. iIntros "H". iSpecialize ("Hcl" with "H"). by iApply fupd_level_fupd.
  Qed.

  Lemma own_inv_to_inv M P: own_inv M P -∗ inv M P.
  Proof.
    iIntros "#I". rewrite inv_eq. iIntros (E H).
    iPoseProof (own_inv_acc0 with "I") as "H"; eauto.
  Qed.

  (** ** Public API of invariants *)
  Global Instance inv_contractive N : Contractive (inv N).
  Proof. rewrite inv_eq. solve_contractive. Qed.

  Global Instance inv_ne N : NonExpansive (inv N).
  Proof. apply contractive_ne, _. Qed.

  Global Instance inv_proper N : Proper (equiv ==> equiv) (inv N).
  Proof. apply ne_proper, _. Qed.

  Global Instance inv_persistent N P : Persistent (inv N P).
  Proof. rewrite inv_eq. apply _. Qed.

  Lemma inv_alter N P Q : inv N P -∗ ▷ □ (P -∗ Q ∗ (Q -∗ P)) -∗ inv N Q.
  Proof.
    rewrite inv_eq. iIntros "#HI #HPQ !>" (E H).
    iMod ("HI" $! E H) as "[HP Hclose]".
    iDestruct ("HPQ" with "HP") as "[$ HQP]".
    iIntros "!> HQ". iApply "Hclose". iApply "HQP". done.
  Qed.

  Lemma inv_iff N P Q : inv N P -∗ ▷ □ (P ↔ Q) -∗ inv N Q.
  Proof.
    iIntros "#HI #HPQ". iApply (inv_alter with "HI").
    iIntros "!> !> HP". iSplitL "HP".
    - by iApply "HPQ".
    - iIntros "HQ". by iApply "HPQ".
  Qed.

  Lemma inv_alloc' k N E P : ▷ P -∗ |k={E}=> inv N P.
  Proof.
    iIntros "HP". iApply own_inv_to_inv.
    iPoseProof (own_inv_alloc0 N E with "HP") as "H".
    iApply (fupd_level_le with "H"). lia.
  Qed.

  Lemma inv_alloc N E P : ▷ P ={E}=∗ inv N P.
  Proof.
    iIntros "HP". iApply own_inv_to_inv.
    iApply (own_inv_alloc N E with "HP").
  Qed.

  Lemma inv_alloc_open0 N E P :
    ↑N ⊆ E → ⊢ |0={E, E∖↑N}=> inv N P ∗ (▷P -∗ |0={E∖↑N, E}=> True).
  Proof.
    iIntros (?). iMod own_inv_alloc_open0 as "[HI $]"; first done.
    iApply own_inv_to_inv. done.
  Qed.

  Lemma inv_alloc_open N E P :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> inv N P ∗ (▷P ={E∖↑N, E}=∗ True).
  Proof.
    iIntros (?). iMod own_inv_alloc_open as "[HI $]"; first done.
    iApply own_inv_to_inv. done.
  Qed.

  Lemma inv_acc0 E N P :
    ↑N ⊆ E → inv N P -∗ |0={E,E∖↑N}=> ▷ P ∗ (▷ P -∗ |0={E∖↑N,E}=> True).
  Proof.
    rewrite inv_eq /inv_def; iIntros (?) "#HI". by iApply "HI".
  Qed.

  Lemma inv_acc E N P :
    ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "Hi". iApply (fupd_level_fupd E _ _ O).
    iMod (inv_acc0 E N P with "Hi") as "($&Hcl)"; first auto.
    iModIntro. iIntros "H". iSpecialize ("Hcl" with "H"). by iApply fupd_level_fupd.
  Qed.

  Lemma inv_combine N1 N2 N P Q :
    N1 ## N2 →
    ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
    inv N1 P -∗ inv N2 Q -∗ inv N (P ∗ Q).
  Proof.
    rewrite inv_eq. iIntros (??) "#HinvP #HinvQ !>"; iIntros (E ?).
    iMod ("HinvP" with "[%]") as "[$ HcloseP]"; first set_solver.
    iMod ("HinvQ" with "[%]") as "[$ HcloseQ]"; first set_solver.
    iMod (fupd_level_mask_subseteq (E ∖ ↑N)) as "Hclose"; first set_solver.
    iIntros "!> [HP HQ]".
    iMod "Hclose" as %_. iMod ("HcloseQ" with "HQ") as %_. by iApply "HcloseP".
  Qed.

  Lemma inv_combine_dup_l N P Q :
    □ (P -∗ P ∗ P) -∗
    inv N P -∗ inv N Q -∗ inv N (P ∗ Q).
  Proof.
    rewrite inv_eq. iIntros "#HPdup #HinvP #HinvQ !>" (E ?).
    iMod ("HinvP" with "[//]") as "[HP HcloseP]".
    iDestruct ("HPdup" with "HP") as "[$ HP]".
    iMod ("HcloseP" with "HP") as %_.
    iMod ("HinvQ" with "[//]") as "[$ HcloseQ]".
    iIntros "!> [HP HQ]". by iApply "HcloseQ".
  Qed.

  (** ** Proof mode integration *)
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

  (** ** Derived properties *)
  Lemma inv_acc_strong E N P :
    ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ ∀ E', ▷ P ={E',↑N ∪ E'}=∗ True.
  Proof.
    iIntros (?) "Hinv".
    iPoseProof (inv_acc (↑ N) N with "Hinv") as "H"; first done.
    rewrite difference_diag_L.
    iPoseProof (fupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
    rewrite left_id_L -union_difference_L //. iMod "H" as "[$ H]"; iModIntro.
    iIntros (E') "HP".
    iPoseProof (fupd_mask_frame_r _ _ E' with "(H HP)") as "H"; first set_solver.
    by rewrite left_id_L.
  Qed.

  Lemma inv_acc_timeless E N P `{!Timeless P} :
    ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ P ∗ (P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "Hinv". iMod (inv_acc with "Hinv") as "[>HP Hclose]"; auto.
    iIntros "!> {$HP} HP". iApply "Hclose"; auto.
  Qed.

  Lemma inv_split_l N P Q : inv N (P ∗ Q) -∗ inv N P.
  Proof.
    iIntros "#HI". iApply inv_alter; eauto.
    iIntros "!> !> [$ $] $".
  Qed.
  Lemma inv_split_r N P Q : inv N (P ∗ Q) -∗ inv N Q.
  Proof.
    rewrite (comm _ P Q). eapply inv_split_l.
  Qed.
  Lemma inv_split N P Q : inv N (P ∗ Q) -∗ inv N P ∗ inv N Q.
  Proof.
    iIntros "#H".
    iPoseProof (inv_split_l with "H") as "$".
    iPoseProof (inv_split_r with "H") as "$".
  Qed.

End inv.
