From iris.algebra Require Export big_op.
From iris.proofmode Require Import tactics.
From Perennial.base_logic Require Import ncfupd.

Set Default Proof Using "Type".

(*! Map filter *)
Section filter.
  Context `{Countable K}.
  Context {A B : Type}.

  Theorem map_filter_lookup_key_in (m : gmap K A) (P : K -> Prop)
      (_ : ∀ (ka : K * A), Decision (P ka.1)) i :
    P i ->
    filter (λ x, P x.1) m !! i = m !! i.
  Proof.
    destruct (m !! i) eqn:He; intros.
    - rewrite map_filter_lookup_Some; eauto.
    - rewrite map_filter_lookup_None; eauto.
  Qed.

  Theorem map_filter_lookup_key_notin (m : gmap K A) (P : K -> Prop)
      (_ : ∀ (ka : K * A), Decision (P ka.1)) i :
    ~ P i ->
    filter (λ x, P x.1) m !! i = None.
  Proof.
    rewrite map_filter_lookup_None; eauto.
  Qed.

  Lemma filter_same_keys_0' (m1 : gmap K A) (m2 : gmap K B) (P : K -> Prop)
                            `{Hdka : ∀ (ka : K * A), Decision (P ka.1)}
                            `{Hdkb : ∀ (kb : K * B), Decision (P kb.1)} :
    (∀ k, is_Some (m1 !! k) -> is_Some (m2 !! k)) ->
    ∀ k, is_Some (filter (λ x, P x.1) m1 !! k) ->
         is_Some (filter (λ x, P x.1) m2 !! k).
  Proof.
    intros.
    destruct H1.
    eapply map_filter_lookup_Some in H1. destruct H1.
    assert (is_Some (m2 !! k)).
    { apply H0. eauto. }
    destruct H3.
    eexists.
    eapply map_filter_lookup_Some. eauto.
  Qed.

  Lemma filter_same_keys_1' (m1 : gmap K A) (m2 : gmap K B) (P : K -> Prop)
                            `{Hdk : ∀ k, Decision (P k)}
                            `{Hdka : ∀ (ka : K * A), Decision (P ka.1)}
                            `{Hdkb : ∀ (kb : K * B), Decision (P kb.1)} :
    (∀ k, is_Some (filter (λ x, P x.1) m1 !! k) ->
          is_Some (filter (λ x, P x.1) m2 !! k)) ->
    (∀ k, is_Some (filter (λ x, ¬ P x.1) m1 !! k) ->
          is_Some (filter (λ x, ¬ P x.1) m2 !! k)) ->
    ∀ k, is_Some (m1 !! k) -> is_Some (m2 !! k).
  Proof.
    intros.
    destruct H2.
    destruct (decide (P k)).
    - edestruct H0.
      { eexists. eapply map_filter_lookup_Some. eauto. }
      eapply map_filter_lookup_Some in H3. intuition eauto.
    - edestruct H1.
      { eexists. eapply map_filter_lookup_Some. eauto. }
      eapply map_filter_lookup_Some in H3. intuition eauto.
  Qed.
End filter.

Lemma filter_same_keys_0 `{Countable K} `(m1 : gmap K A) `(m2 : gmap K B) (P : K -> Prop)
                         `{Hdka : ∀ (ka : K * A), Decision (P ka.1)}
                         `{Hdkb : ∀ (kb : K * B), Decision (P kb.1)} :
  (∀ k, is_Some (m1 !! k) <-> is_Some (m2 !! k)) ->
  ∀ k, is_Some (filter (λ x, P x.1) m1 !! k) <->
       is_Some (filter (λ x, P x.1) m2 !! k).
Proof.
  split.
  - apply filter_same_keys_0'. intros. eapply H0. eauto.
  - apply filter_same_keys_0'. intros. eapply H0. eauto.
Qed.

Lemma filter_same_keys_1 `{Countable K} `(m1 : gmap K A) `(m2 : gmap K B) (P : K -> Prop)
                         `{Hdk : ∀ k, Decision (P k)}
                         `{Hdka : ∀ (ka : K * A), Decision (P ka.1)}
                         `{Hdkb : ∀ (kb : K * B), Decision (P kb.1)} :
  (∀ k, is_Some (filter (λ x, P x.1) m1 !! k) <->
        is_Some (filter (λ x, P x.1) m2 !! k)) ->
  (∀ k, is_Some (filter (λ x, ¬ P x.1) m1 !! k) <->
        is_Some (filter (λ x, ¬ P x.1) m2 !! k)) ->
  ∀ k, is_Some (m1 !! k) <-> is_Some (m2 !! k).
Proof.
  split.
  - eapply filter_same_keys_1'; eauto.
    + intros; eapply H0; eauto.
    + intros; eapply H1; eauto.
  - eapply filter_same_keys_1'; eauto.
    + intros; eapply H0; eauto.
    + intros; eapply H1; eauto.
Qed.

Lemma dom_filter_eq `{Countable K} `(m1 : gmap K A) `(m2 : gmap K B) (P : K -> Prop)
                    `{Hdk : ∀ k, Decision (P k)} :
  dom (gset K) m1 = dom (gset K) m2 ->
  dom (gset K) (filter (λ x, P x.1) m1) = dom (gset K) (filter (λ x, P x.1) m2).
Proof.
  intros.
  apply set_eq.
  setoid_rewrite elem_of_dom.
  eapply filter_same_keys_0.
  setoid_rewrite <- elem_of_dom. rewrite H0. eauto.
Qed.

(*! map_zip *)
Section map_zip.
  Context `{Countable K}.
  Context {A B: Type}.

  Theorem map_zip_empty_l (m2 : gmap K B) :
    map_zip (∅ : gmap K A) m2 = ∅.
  Proof.
    rewrite /map_zip.
    apply map_eq; intros.
    erewrite lookup_merge by reflexivity.
    rewrite !lookup_empty; eauto.
  Qed.

  Theorem map_zip_empty_r (m1 : gmap K A) :
    map_zip m1 (∅ : gmap K B) = ∅.
  Proof.
    rewrite /map_zip.
    apply map_eq; intros.
    erewrite lookup_merge by reflexivity.
    rewrite !lookup_empty; eauto.
    destruct (m1 !! i); eauto.
  Qed.

  Theorem map_zip_insert (m1 : gmap K A) (m2 : gmap K B) i v1 v2 :
    map_zip (<[i:=v1]> m1) (<[i:=v2]> m2) =
    <[i:=(v1, v2)]> (map_zip m1 m2).
  Proof.
    rewrite /map_zip.
    apply map_eq; intros.
    destruct (decide (i = i0)); subst.
    - erewrite lookup_merge by reflexivity.
      rewrite !lookup_insert. eauto.
    - erewrite lookup_merge by reflexivity.
      rewrite !lookup_insert_ne; eauto.
      erewrite lookup_merge by reflexivity.
      eauto.
  Qed.

  Theorem map_zip_lookup_none_1 (m1 : gmap K A) (m2 : gmap K B) i :
    m1 !! i = None ->
    map_zip m1 m2 !! i = None.
  Proof.
    intros; rewrite /map_zip.
    erewrite lookup_merge by reflexivity.
    rewrite H0; eauto.
  Qed.

  Theorem map_zip_lookup_none_2 (m1 : gmap K A) (m2 : gmap K B) i :
    m2 !! i = None ->
    map_zip m1 m2 !! i = None.
  Proof.
    intros; rewrite /map_zip.
    erewrite lookup_merge by reflexivity.
    destruct (m1 !! i); eauto; rewrite H0; eauto.
  Qed.

  Theorem map_zip_lookup_some (m1 : gmap K A) (m2 : gmap K B) i v1 v2:
    m1 !! i = Some v1 ->
    m2 !! i = Some v2 ->
    map_zip m1 m2 !! i = Some (v1, v2).
  Proof.
    intros; rewrite /map_zip.
    erewrite lookup_merge by reflexivity.
    rewrite H0 H1. eauto.
  Qed.

  Theorem map_zip_filter (m1 : gmap K A) (m2 : gmap K B) (P : K -> Prop)
    `{Hdk : ∀ k, Decision (P k)}
    `{Hdka : ∀ (ka : K * A), Decision (P ka.1)}
    `{Hdkb : ∀ (kb : K * B), Decision (P kb.1)}
    `{Hdkab : ∀ (kab : K * (A * B)), Decision (P kab.1)} :
    map_zip (filter (λ x, P x.1) m1) (filter (λ x, P x.1) m2) =
    filter (λ x, P x.1) (map_zip m1 m2).
  Proof.
    rewrite /map_zip.
    apply map_eq; intros.
    erewrite lookup_merge by reflexivity.
    destruct (decide (P i)).
    - rewrite !map_filter_lookup_key_in; eauto.
      erewrite lookup_merge by reflexivity; eauto.
    - rewrite !map_filter_lookup_key_notin; eauto.
  Qed.
End map_zip.

(*! big_sepM *)
Section bi.
Context {PROP:bi} `{!BiAffine PROP}.

Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.

Section map.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  Lemma big_sepS_exists_sepM Φ (s : gset K) :
    ([∗ set] k ∈ s, ∃ v, Φ k v) -∗ ∃ m, ⌜ dom (gset _) m = s ⌝ ∗ ([∗ map] k ↦ v ∈ m, Φ k v).
  Proof using BiAffine0.
    iIntros "Hs".
    iInduction s as [| k s'] "IH" using set_ind_L.
    - iExists ∅. rewrite dom_empty_L; eauto.
    - rewrite big_sepS_union; last by set_solver.
      iDestruct "Hs" as "(Hsingle&Hs)".
      iDestruct ("IH" with "Hs") as (m Hdom) "H".
      rewrite big_sepS_singleton. iDestruct "Hsingle" as (v) "HΦ".
      iExists (<[k:=v]> m). iSplit.
      * rewrite dom_insert_L. iPureIntro. set_solver.
      * rewrite big_sepM_insert; first by iFrame.
        apply not_elem_of_dom. set_solver.
  Qed.

  Lemma big_sepM_mono_with_inv' P Φ Ψ m :
    (∀ k x, m !! k = Some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) →
    P ∗ ([∗ map] k ↦ x ∈ m, Φ k x) ⊢ P ∗ [∗ map] k ↦ x ∈ m, Ψ k x.
  Proof using BiAffine0.
    intros Hwand.
    induction m as [|i x m ? IH] using map_ind; auto using big_sepM_empty'.
    by rewrite big_opM_eq.
    rewrite ?big_sepM_insert //.
    iIntros "(HP&Hi&H)".
    iDestruct (Hwand with "[$]") as "(?&$)".
    { by rewrite lookup_insert. }
    iApply IH; eauto.
    { iIntros (k x' Hlookup). iApply Hwand.
      destruct (decide (i = k)).
      - subst. congruence.
      - rewrite lookup_insert_ne //.
    }
    iFrame.
  Qed.

  Lemma big_sepM_mono_with_inv P Φ Ψ m :
    (∀ k x, m !! k = Some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) →
    P -∗ ([∗ map] k ↦ x ∈ m, Φ k x) -∗ P ∗ [∗ map] k ↦ x ∈ m, Ψ k x.
  Proof using BiAffine0.
    iIntros (?) "HP H". iApply (big_sepM_mono_with_inv' with "[HP H]"); eauto.
    iFrame.
  Qed.

  Lemma big_sepM_mono_wand `{!BiAffine PROP} Φ Ψ m (I : PROP) :
    □ ( ∀ k x, ⌜ m !! k = Some x ⌝ -∗
      I ∗ Φ k x -∗ I ∗ Ψ k x ) -∗
    I ∗ ([∗ map] k↦x ∈ m, Φ k x) -∗
    I ∗ ([∗ map] k↦x ∈ m, Ψ k x).
  Proof.
    iIntros "#Hwand [HI Hm]".
    iInduction m as [|i x m] "IH" using map_ind.
    - iFrame. iApply big_sepM_empty. done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      iDestruct ("Hwand" with "[] [$HI $Hi]") as "[HI Hi]".
      { rewrite lookup_insert. eauto. }
      iDestruct ("IH" with "[Hwand] HI Hm") as "[HI Hm]".
      { iModIntro. iIntros (k x0 Hkx0) "[HI Hk]".
        destruct (decide (k = i)); subst; try congruence.
        iApply ("Hwand" with "[]").
        { rewrite lookup_insert_ne; eauto. }
        iFrame.
      }
      iFrame. iApply big_sepM_insert; eauto. iFrame.
  Qed.

  Lemma big_sepM_mono_fupd `{!BiAffine PROP} `{!BiFUpd PROP} Φ Ψ m (I : PROP) E :
   □ ( ∀ k x, ⌜ m !! k = Some x ⌝ →
      I ∗ Φ k x ={E}=∗ I ∗ Ψ k x ) -∗
    I ∗ ([∗ map] k↦x ∈ m, Φ k x) ={E}=∗
    I ∗ ([∗ map] k↦x ∈ m, Ψ k x).
  Proof.
    iIntros "#Hfupd [HI Hm]".
    iInduction m as [|i x m] "IH" using map_ind.
    - iModIntro. iFrame. iApply big_sepM_empty. done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      iMod ("Hfupd" with "[] [$HI $Hi]") as "[HI Hi]".
      { rewrite lookup_insert. eauto. }
      iMod ("IH" with "[Hfupd] HI Hm") as "[HI Hm]".
      { iModIntro. iIntros (k x0 Hkx0) "[HI Hk]".
        destruct (decide (k = i)); subst; try congruence.
        iApply "Hfupd".
        { rewrite lookup_insert_ne; eauto. }
        iFrame.
      }
      iFrame. iApply big_sepM_insert; eauto. iFrame. done.
  Qed.

  Lemma big_sepM_lookup_holds
        `{BiAffine PROP} (m: gmap K A) :
    ⊢@{PROP} [∗ map] k↦v ∈ m, ⌜m !! k = Some v⌝.
  Proof using BiAffine0.
    iPureIntro.
    apply map_Forall_lookup; auto.
  Qed.

  Lemma big_sepM_subseteq_diff `{!BiAffine PROP} Φ m1 m2 :
    m2 ⊆ m1 ->
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    ([∗ map] k↦x ∈ m2, Φ k x) ∗
    ([∗ map] k↦x ∈ m1 ∖ m2, Φ k x).
  Proof.
    iIntros (Hsubset) "Hm".
    replace (m1) with (m2 ∪ m1 ∖ m2) at 1.
    2: { rewrite map_difference_union; eauto. }
    iDestruct (big_sepM_union with "Hm") as "[Hm1 Hm2]".
    { apply map_disjoint_difference_r; eauto. }
    iFrame.
  Qed.

  Lemma big_sepM_subseteq_acc `{!BiAffine PROP} Φ m1 m2 :
    m2 ⊆ m1 ->
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    ([∗ map] k↦x ∈ m2, Φ k x) ∗
    (([∗ map] k↦x ∈ m2, Φ k x) -∗
     [∗ map] k↦x ∈ m1, Φ k x).
  Proof.
    iIntros (Hsubseteq) "Hm1".
    iDestruct (big_sepM_subseteq_diff with "Hm1") as "[Hm2 Hm12]"; eauto.
    iFrame "Hm2".
    iIntros "Hm2".
    iDestruct (big_sepM_union with "[$Hm2 $Hm12]") as "Hm1".
    { eapply map_disjoint_difference_r; eauto. }
    rewrite map_difference_union; eauto.
  Qed.

  Lemma big_sepM_filter_split Φ (P : (K * A) -> Prop) m
                         `{! ∀ ka, Decision (P ka)} :
    ⊢
    ( [∗ map] k↦x ∈ m, Φ k x ) ∗-∗
    ( ( [∗ map] k↦x ∈ filter (λ x, P x) m, Φ k x ) ∗
      ( [∗ map] k↦x ∈ filter (λ x, ~P x) m, Φ k x ) ).
  Proof using BiAffine0.
    iSplit.
    - iIntros "Hm".
      erewrite <- (map_filter_union_complement (λ x, P x) m) at 1.
      iDestruct (big_sepM_union with "Hm") as "[Hmp Hmnp]".
      { eapply map_disjoint_filter_complement. }
      iFrame.
    - iIntros "[Hm1 Hm2]".
      iDestruct (big_sepM_union with "[$Hm1 $Hm2]") as "Hm".
      { eapply map_disjoint_filter_complement. }
      rewrite map_filter_union_complement. iFrame.
  Qed.

  Lemma big_sepM_mono_gen_Q {B} (Q : PROP) (Φ : K->A->PROP) (Ψ : K->B->PROP) (m1 : gmap K A) (m2 : gmap K B) :
    ⌜ ∀ k, m1 !! k = None -> m2 !! k = None ⌝ -∗
    □ ( ∀ k x1,
        ⌜ m1 !! k = Some x1 ⌝ -∗
        (Q ∗ Φ k x1) -∗
        ∃ x2,
        ⌜ m2 !! k = Some x2 ⌝ ∗
        (Q ∗ Ψ k x2) ) -∗
    (Q ∗ [∗ map] k↦x ∈ m1, Φ k x) -∗
    (Q ∗ [∗ map] k↦x ∈ m2, Ψ k x).
  Proof using BiAffine0.
    iIntros "#Hnone #Hsome [HQ Hm]".
    iInduction m1 as [|i x m] "IH" using map_ind forall (m2).
    - iFrame "HQ".
      iAssert (⌜m2 = ∅⌝)%I as "->".
      2: iApply big_sepM_empty; done.
      iDestruct "Hnone" as "%Hnone".
      iPureIntro. apply map_eq; intros i. rewrite lookup_empty. eauto.
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      iDestruct ("Hsome" with "[] [$HQ $Hi]") as (x2) "[% [HQ Hi]]".
      { rewrite lookup_insert; done. }
      replace m2 with (<[i := x2]> (delete i m2)).
      2: { rewrite insert_delete insert_id; eauto. }
      iDestruct ("IH" $! (delete i m2) with "[] [] HQ Hm") as "[HQ Hm]".
      { iDestruct "Hnone" as "%Hnone".
        iPureIntro. intros k Hk. destruct (decide (i = k)); subst.
        { rewrite lookup_delete; done. }
        specialize (Hnone k). repeat rewrite -> lookup_insert_ne in Hnone by eauto.
        eauto.
      }
      {
        iModIntro. iIntros (k kx Hkx) "H".
        iDestruct ("Hsome" with "[] H") as (x0) "[% H]".
        { destruct (decide (i = k)); subst.
          { rewrite lookup_insert; iPureIntro; congruence. }
          rewrite lookup_insert_ne; eauto.
        }
        iExists _. iFrame.
        destruct (decide (i = k)); subst; try congruence.
        rewrite lookup_delete_ne; eauto.
        rewrite -> lookup_insert_ne in H2 by eauto.
        rewrite -> lookup_delete_ne in H2 by eauto.
        done.
      }
      iFrame.
      iApply big_sepM_insert.
      { rewrite lookup_delete; eauto. }
      iFrame.
  Qed.

  Lemma big_sepM_mono_gen {B} (Φ : K->A->PROP) (Ψ : K->B->PROP) (m1 : gmap K A) (m2 : gmap K B) :
    ⌜ ∀ k, m1 !! k = None -> m2 !! k = None ⌝ -∗
    □ ( ∀ k x1,
        ⌜ m1 !! k = Some x1 ⌝ -∗
        Φ k x1 -∗
        ∃ x2,
        ⌜ m2 !! k = Some x2 ⌝ ∗
        Ψ k x2 ) -∗
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    ([∗ map] k↦x ∈ m2, Ψ k x).
  Proof using BiAffine0.
    iIntros "#Hnone #Hsome Hm".
    iDestruct (big_sepM_mono_gen_Q emp%I with "Hnone [Hsome] [Hm]") as "[_ Hm]"; iFrame.
    iIntros (k x Hkx). iModIntro. iIntros "[_ H]".
    iDestruct ("Hsome" $! k x Hkx with "H") as (x2) "[% H]".
    iExists x2. iSplit; first done. iSplit; first done. iExact "H".
  Qed.

  Lemma big_sepM_mono_dom_Q {B} (Q : PROP) (Φ : K->A->PROP) (Ψ : K->B->PROP) (m1 : gmap K A) (m2 : gmap K B) :
    dom (gset K) m1 = dom (gset K) m2 ->
    □ ( ∀ k x1,
        ⌜ m1 !! k = Some x1 ⌝ -∗
        (Q ∗ Φ k x1) -∗
        ∃ x2,
        ⌜ m2 !! k = Some x2 ⌝ ∗
        (Q ∗ Ψ k x2) ) -∗
    (Q ∗ [∗ map] k↦x ∈ m1, Φ k x) -∗
    (Q ∗ [∗ map] k↦x ∈ m2, Ψ k x).
  Proof using BiAffine0.
    iIntros (Hnone).
    iApply big_sepM_mono_gen_Q.
    iPureIntro. intros k Hk.
    apply not_elem_of_dom in Hk. rewrite Hnone in Hk. apply not_elem_of_dom in Hk. done.
  Qed.

  Lemma big_sepM_mono_dom {B} (Φ : K->A->PROP) (Ψ : K->B->PROP) (m1 : gmap K A) (m2 : gmap K B) :
    dom (gset K) m1 = dom (gset K) m2 ->
    □ ( ∀ k x1,
        ⌜ m1 !! k = Some x1 ⌝ -∗
        Φ k x1 -∗
        ∃ x2,
        ⌜ m2 !! k = Some x2 ⌝ ∗
        Ψ k x2 ) -∗
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    ([∗ map] k↦x ∈ m2, Ψ k x).
  Proof using BiAffine0.
    iIntros (Hnone).
    iApply big_sepM_mono_gen.
    iPureIntro. intros k Hk.
    apply not_elem_of_dom in Hk. rewrite Hnone in Hk. apply not_elem_of_dom in Hk. done.
  Qed.

End map.

Section iprop_map.

  Context `{invGS Σ, crashG Σ}.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → iProp Σ.

  Lemma big_sepM_mono_ncfupd `{invGS Σ, crashG Σ} Φ Ψ m (I : iProp Σ) E :
   □ ( ∀ k x, ⌜ m !! k = Some x ⌝ →
      I ∗ Φ k x -∗ |NC={E}=> I ∗ Ψ k x ) -∗
    I ∗ ([∗ map] k↦x ∈ m, Φ k x) -∗ |NC={E}=>
    I ∗ ([∗ map] k↦x ∈ m, Ψ k x).
  Proof.
    iIntros "#Hfupd [HI Hm]".
    iInduction m as [|i x m] "IH" using map_ind.
    - iModIntro. iFrame. iApply big_sepM_empty. done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      iMod ("Hfupd" with "[] [$HI $Hi]") as "[HI Hi]".
      { rewrite lookup_insert. eauto. }
      iMod ("IH" with "[Hfupd] HI Hm") as "[HI Hm]".
      { iModIntro. iIntros (k x0 Hkx0) "[HI Hk]".
        destruct (decide (k = i)); subst; try congruence.
        iApply "Hfupd".
        { rewrite lookup_insert_ne; eauto. }
        iFrame.
      }
      iFrame. iApply big_sepM_insert; eauto. iFrame. done.
  Qed.
End iprop_map.

Section map2.
  Context `{Countable K} {A B : Type}.
  Implicit Types Φ Ψ : K → A → B → PROP.

  Lemma big_sepM2_lookup_l_some
      Φ (m1 : gmap K A) (m2 : gmap K B) (i : K) (x1 : A)
      (_ : forall x2 : B, Absorbing (Φ i x1 x2)) :
    m1 !! i = Some x1 ->
      ⊢ ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
          ⌜∃ x2, m2 !! i = Some x2⌝.
  Proof using BiAffine0.
    intros.
    iIntros "H".
    iDestruct (big_sepM2_lookup_l with "H") as (x2) "[% _]"; eauto.
  Qed.

  Lemma big_sepM2_lookup_r_some
      Φ (m1 : gmap K A) (m2 : gmap K B) (i : K) (x2 : B)
      (_ : forall x1 : A, Absorbing (Φ i x1 x2)) :
    m2 !! i = Some x2 ->
      ⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
          ⌜∃ x1, m1 !! i = Some x1⌝.
  Proof using BiAffine0.
    intros.
    iIntros "H".
    iDestruct (big_sepM2_lookup_r with "H") as (x1) "[% _]"; eauto.
  Qed.

  Lemma big_sepM2_lookup_l_none
      Φ (m1 : gmap K A) (m2 : gmap K B) (i : K)
      (_ : forall (x1 : A) (x2 : B), Absorbing (Φ i x1 x2)) :
    m1 !! i = None ->
      ⊢ ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
          ⌜m2 !! i = None⌝.
  Proof using BiAffine0.
    case_eq (m2 !! i); auto.
    iIntros (? ? ?) "H".
    iDestruct (big_sepM2_lookup_r with "H") as (x2) "[% _]"; eauto; congruence.
  Qed.

  Lemma big_sepM2_lookup_r_none
      Φ (m1 : gmap K A) (m2 : gmap K B) (i : K)
      (_ : forall (x1 : A) (x2 : B), Absorbing (Φ i x1 x2)) :
    m2 !! i = None ->
      ⊢ ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
          ⌜m1 !! i = None⌝.
  Proof using BiAffine0.
    case_eq (m1 !! i); auto.
    iIntros (? ? ?) "H".
    iDestruct (big_sepM2_lookup_l with "H") as (x1) "[% _]"; eauto; congruence.
  Qed.

  Lemma big_sepM2_sepM_1
      Φ (m1 : gmap K A) (m2 : gmap K B)
      (_ : forall i x1 x2, Absorbing (Φ i x1 x2)) :
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
      ( [∗ map] k↦y1 ∈ m1, ∃ y2, ⌜ m2 !! k = Some y2 ⌝ ∗ Φ k y1 y2 ).
  Proof using BiAffine0.
    iIntros "H".
    rewrite <- (list_to_map_to_list m1).
    pose proof (NoDup_fst_map_to_list m1); revert H1.
    generalize (map_to_list m1); intros l H1.
    iInduction l as [|] "Hi" forall (m2).
    - iDestruct (big_sepM2_empty_r with "H") as %->.
      simpl.
      iDestruct (big_sepM2_empty with "H") as "H".
      iApply big_sepM_empty; iFrame.
    - simpl.
      iDestruct (big_sepM2_lookup_l_some with "H") as %H2.
      { apply lookup_insert. }
      destruct H2.
      rewrite <- insert_delete at 1.
      replace m2 with (<[a.1 := x]> m2).
      2: {
        rewrite insert_id //.
      }
      iDestruct (big_sepM2_insert_delete with "H") as "[Ha H]".
      inversion H1; clear H1; subst.
      iApply big_sepM_insert.
      { apply not_elem_of_list_to_map_1; eauto. }
      iSplitL "Ha".
      { iExists _. iFrame. rewrite insert_id; done. }
      rewrite delete_idemp.
      iSpecialize ("Hi" $! H6).
      rewrite delete_notin.
      2: { apply not_elem_of_list_to_map_1; eauto. }
      iDestruct ("Hi" with "H") as "H".
      iApply (big_sepM_mono with "H").
      iIntros (k x0 Hk) "H".
      iDestruct "H" as (y2) "[% H]".
      iExists _; iFrame.
      iPureIntro.
      assert (a.1 ≠ k).
      { intro He; subst.
        rewrite lookup_delete in H1; congruence. }
      rewrite -> lookup_insert_ne by eauto.
      rewrite -> lookup_delete_ne in H1 by eauto.
      eauto.
  Qed.

  (* FIXME: shadows / shadowed by an Iris lemma *)
  Lemma big_sepM2_sepM_2
      Φ (m1 : gmap K A) (m2 : gmap K B)
      (_ : forall i x1 x2, Absorbing (Φ i x1 x2)) :
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
      ( [∗ map] k↦y2 ∈ m2, ∃ y1, ⌜ m1 !! k = Some y1 ⌝ ∗ Φ k y1 y2 ).
  Proof using BiAffine0.
    iIntros "H".
    rewrite <- (list_to_map_to_list m2).
    pose proof (NoDup_fst_map_to_list m2); revert H1.
    generalize (map_to_list m2); intros l H1.
    iInduction l as [|] "Hi" forall (m1).
    - iDestruct (big_sepM2_empty_l with "H") as %->.
      simpl.
      iDestruct (big_sepM2_empty with "H") as "H".
      iApply big_sepM_empty; iFrame.
    - simpl.
      iDestruct (big_sepM2_lookup_r_some with "H") as %H2.
      { apply lookup_insert. }
      destruct H2.
      rewrite <- insert_delete at 1.
      replace m1 with (<[a.1 := x]> m1).
      2: {
        rewrite insert_id //.
      }
      iDestruct (big_sepM2_insert_delete with "H") as "[Ha H]".
      inversion H1; clear H1; subst.
      iApply big_sepM_insert.
      { apply not_elem_of_list_to_map_1; eauto. }
      iSplitL "Ha".
      { iExists _. iFrame. rewrite insert_id; done. }
      rewrite delete_idemp.
      iSpecialize ("Hi" $! H6).
      rewrite (delete_notin (list_to_map l)).
      2: { apply not_elem_of_list_to_map_1; eauto. }
      iDestruct ("Hi" with "H") as "H".
      iApply (big_sepM_mono with "H").
      iIntros (k x0 Hk) "H".
      iDestruct "H" as (y1) "[% H]".
      iExists _; iFrame.
      iPureIntro.
      assert (a.1 ≠ k).
      { intro He; subst.
        rewrite lookup_delete in H1; congruence. }
      rewrite -> lookup_insert_ne by eauto.
      rewrite -> lookup_delete_ne in H1 by eauto.
      eauto.
  Qed.

  Lemma big_sepM_sepM2_exists Φ (m1 : gmap K A)
      (_ : forall i x1 x2, Absorbing (Φ i x1 x2)) :
    ( [∗ map] k↦y1 ∈ m1, ∃ y2, Φ k y1 y2 ) -∗
    ∃ m2, ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ).
  Proof using BiAffine0.
    iIntros "Hm".
    iInduction m1 as [|i x m] "IH" using map_ind.
    - iExists ∅. iApply big_sepM2_empty. done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      iDestruct "Hi" as (y2) "Hi".
      iDestruct ("IH" with "Hm") as (m2) "Hm".
      iExists (<[i := y2]> m2).
      iDestruct (big_sepM2_lookup_l_none with "Hm") as "%Hm2i"; eauto.
      iApply big_sepM2_insert; eauto.
      iFrame.
  Qed.

  Lemma big_sepM_sepM2_merge (Φ : K -> A -> PROP) (Ψ : K -> B -> PROP)
    (m1 : gmap K A) (m2 : gmap K B) :
    dom (gset K) m1 = dom (gset K) m2 ->
    ( [∗ map] k↦y1 ∈ m1, Φ k y1 ) ∗
    ( [∗ map] k↦y2 ∈ m2, Ψ k y2 ) -∗
    [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 ∗ Ψ k y2.
  Proof using BiAffine0.
    iIntros (Hdom) "[Hm1 Hm2]".
    iApply big_sepM2_sepM; last by iFrame.
    intros k. rewrite -!elem_of_dom Hdom. auto.
  Qed.

  Lemma big_sepM_sepM2_merge_ex (Φ : K -> A -> B -> PROP) (m1 : gmap K A) (m2 : gmap K B) :
    dom (gset K) m1 = dom (gset K) m2 ->
    ( [∗ map] k↦y1 ∈ m1, ∃ y2, ⌜m2 !! k = Some y2⌝ ∗ Φ k y1 y2 ) -∗
    [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2.
  Proof using BiAffine0.
    iIntros (Hdom) "Hm".
    iDestruct (big_sepM_sepM2_merge _ (λ _ _, emp)%I with "[Hm]") as "Hm"; eauto.
    iApply (big_sepM2_mono with "Hm").
    iIntros (k y1 y2 Hky1 Hky2) "[H _]".
    iDestruct "H" as (y0) "[% H]".
    rewrite H0 in Hky2. inversion Hky2; subst. iFrame.
  Qed.

  Lemma big_sepM2_sepM_merge Φ (Ψ : K -> A -> PROP) (m1 : gmap K A) (m2 : gmap K B)
      (_ : forall i x1 x2, Absorbing (Φ i x1 x2)) :
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) ∗
    ( [∗ map] k↦y1 ∈ m1, Ψ k y1 ) -∗
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ∗ Ψ k y1 ).
  Proof using BiAffine0.
    iIntros "[Hm2 Hm]".
    iInduction m1 as [|i x m] "IH" using map_ind forall (m2).
    - iDestruct (big_sepM2_empty_r with "Hm2") as "%He". subst. iApply big_sepM2_empty. done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      iDestruct (big_sepM2_lookup_l_some _ _ _ i with "Hm2") as (x2) "%Hm2i"; eauto.
      { rewrite lookup_insert; eauto. }
      replace (m2) with (<[i:=x2]> (delete i m2)).
      2: { rewrite insert_delete insert_id //. }
      iDestruct (big_sepM2_insert with "Hm2") as "[Hii Hm2]"; eauto.
      { rewrite lookup_delete; eauto. }
      iDestruct ("IH" with "Hm2 Hm") as "Hm2".
      iApply big_sepM2_insert; eauto.
      { rewrite lookup_delete; eauto. }
      iFrame.
  Qed.

  Lemma big_sepM2_filter Φ (P : K -> Prop) (m1 : gmap K A) (m2 : gmap K B)
                         `{! ∀ k, Decision (P k)} :
    ⊢
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) ∗-∗
    ( ( [∗ map] k↦y1;y2 ∈ filter (λ x, P x.1) m1;filter (λ x, P x.1) m2, Φ k y1 y2 ) ∗
      ( [∗ map] k↦y1;y2 ∈ filter (λ x, ~P x.1) m1;filter (λ x, ~P x.1) m2, Φ k y1 y2 ) ).
  Proof using BiAffine0.
    rewrite big_sepM2_eq /big_sepM2_def.
    iSplit.
    - iIntros "[% Hm]".
      erewrite <- (map_filter_union_complement _ (map_zip m1 m2)).
      iDestruct (big_sepM_union with "Hm") as "[Hmp Hmnp]".
      { eapply map_disjoint_filter_complement. }
      iSplitL "Hmp".
      + iSplit.
        { iPureIntro; eapply filter_same_keys_0; eauto. }
        rewrite map_zip_filter. iFrame.
      + iSplit.
        { iPureIntro.
          eapply (filter_same_keys_0 _ _ (λ k, ¬ P k)). eauto. }
        rewrite (map_zip_filter _ _ (λ k, ¬ P k)). iFrame.
    - iIntros "[[% Hm1] [% Hm2]]".
      iSplit.
      { iPureIntro. eapply filter_same_keys_1; eauto. }
      rewrite map_zip_filter.
      rewrite (map_zip_filter _ _ (λ k, ¬ P k)).
      iDestruct (big_sepM_union with "[$Hm1 $Hm2]") as "Hm".
      { eapply map_disjoint_filter_complement. }
      rewrite map_filter_union_complement. iFrame.
  Unshelve.
    all: typeclasses eauto.
  Qed.

  Lemma big_sepM2_insert_left_inv Φ (m1 : gmap K A) (m2 : gmap K B) k a :
    m1 !! k = None →
    ([∗ map] k↦y1;y2 ∈ <[k := a]>m1; m2, Φ k y1 y2) -∗
    ∃ b, ⌜ m2 !! k = Some b ⌝ ∗ Φ k a b ∗ [∗ map] k↦y1;y2 ∈ m1; delete k m2, Φ k y1 y2.
  Proof using BiAffine0.
    iIntros (Hone) "H".
    iDestruct (big_sepM2_dom with "H") as %Hdom.
    assert (∃ b, m2 !! k = Some b) as (b&Hlookup).
    { apply elem_of_dom. rewrite -Hdom. set_solver. }
    rewrite -(insert_id m2 k b) //.
    rewrite big_sepM2_insert_delete.
    iDestruct "H" as "(HΦ&H)".
    iExists b. iFrame. iSplit.
    { rewrite lookup_insert //. }
    rewrite delete_notin // delete_insert_delete //.
  Qed.
End map2.

Section gmap_curry.

  Context `{EqDecision A} `{Countable A}.
  Context `{EqDecision B} `{Countable B}.
  Variable (T : Type).

  Theorem gmap_uncurry_insert (m : gmap (A * B) T) (k : A * B) (v : T) :
    m !! k = None ->
    gmap_uncurry (<[k:=v]> m) =
      <[fst k :=
        <[snd k := v]> (default ∅ ((gmap_uncurry m) !! fst k))]>
      (gmap_uncurry m).
  Proof.
    intros.
    destruct k as [b o].
    rewrite /gmap_uncurry.
    rewrite map_fold_insert_L; eauto.
    2: {
      intros.
      destruct j1, j2.
      destruct (decide (a = a0)); subst.
      - repeat rewrite <- partial_alter_compose.
        apply partial_alter_ext.
        destruct x; intros; simpl.
        + rewrite insert_commute; eauto. congruence.
        + rewrite insert_commute; eauto. congruence.
      - rewrite partial_alter_commute; eauto.
    }

    simpl.
    eapply partial_alter_ext; intros.
    rewrite H2. reflexivity.
  Qed.

  Theorem gmap_uncurry_insert_delete (m : gmap (A * B) T) (k : A * B) (v : T) :
    m !! k = None ->
    gmap_uncurry (<[k:=v]> m) =
      <[fst k :=
        <[snd k := v]> (default ∅ ((gmap_uncurry m) !! fst k))]>
      (delete (fst k) (gmap_uncurry m)).
  Proof.
    intros.
    rewrite gmap_uncurry_insert //. rewrite insert_delete //.
  Qed.

  Theorem gmap_uncurry_lookup_exists (m : gmap (A * B) T) (k : A * B) (v : T) :
    m !! k = Some v ->
    ∃ offmap,
      gmap_uncurry m !! (fst k) = Some offmap ∧
      offmap !! (snd k) = Some v.
  Proof.
    intros.
    destruct k.
    destruct (gmap_uncurry m !! a) eqn:He.
    - eexists; intuition eauto.
      rewrite -lookup_gmap_uncurry in H1.
      rewrite He in H1; simpl in H1. eauto.
    - exfalso. simpl in He.
      pose proof (lookup_gmap_uncurry_None m a). destruct H2.
      rewrite H2 in H1; eauto. congruence.
  Qed.

  Theorem gmap_uncurry_lookup (m : gmap (A * B) T) (k1 : A) (k2 : B) (offmap : gmap B T) :
    gmap_uncurry m !! k1 = Some offmap →
    m !! (k1, k2) = offmap !! k2.
  Proof.
    intros Hacc.
    rewrite -lookup_gmap_uncurry Hacc //=.
  Qed.

End gmap_curry.

(* TODO(joe): got halfway through this before I realized gmap_addr_by_block_big_sepM exists *)
Lemma big_sepM_gmap_uncurry `{Countable K1} `{Countable K2} {X : Type}
      (m: gmap (K1*K2) X) (Φ : K1 → K2 → X → PROP) :
  ([∗ map] k↦y ∈ m, Φ (fst k) (snd k) y) -∗
  ([∗ map] k1↦m1' ∈ gmap_uncurry m, [∗ map] k2↦y ∈ m1', Φ k1 k2 y)%I.
Proof.
  iIntros "H".
  iInduction m as [| i x m1] "IH" using map_ind.
  * rewrite /gmap_uncurry //=.
  * rewrite big_sepM_insert //.
    iDestruct "H" as "(HΦ&H)".
    rewrite ?gmap_uncurry_insert_delete //; last first.
    iDestruct ("IH" with "H") as "H".
    rewrite big_sepM_insert ?lookup_delete //.
    destruct (gmap_uncurry m1 !! i.1) as [m1'|] eqn:Hlookup.
    ** assert (Hdel: gmap_uncurry m1 = <[i.1 := m1']> (delete i.1 (gmap_uncurry m1))).
       { rewrite insert_delete insert_id //=. }
       iEval (rewrite Hdel) in "H".
       rewrite big_sepM_insert ?lookup_delete //.
       iDestruct "H" as "(H1&H2)".
       iFrame. simpl. rewrite big_sepM_insert; first by iFrame.
       destruct i as (i1&i2).
       rewrite -lookup_gmap_uncurry in H1.
       rewrite Hlookup /= in H1.
       eauto.
    **
Abort.

End bi.
