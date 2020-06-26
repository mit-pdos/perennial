From iris.algebra Require Export big_op.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

Set Default Proof Using "Type*".
Local Existing Instances monoid_ne monoid_assoc monoid_comm
  monoid_left_id monoid_right_id monoid_proper
  monoid_homomorphism_rel_po monoid_homomorphism_rel_proper
  monoid_homomorphism_op_proper
  monoid_homomorphism_ne weak_monoid_homomorphism_proper.

From iris.bi Require Import derived_laws plainly big_op.
Import interface.bi derived_laws.bi.

Lemma elem_of_map_list {A B} (l : list A) (f : A -> B) a :
  a ∈ map f l ->
  ∃ b, b ∈ l ∧ f b = a.
Proof.
  induction l; simpl; intros.
  - inversion H.
  - inversion H; subst; intuition.
    + exists a0; intuition. apply elem_of_list_here.
    + destruct H0 as [b H0].
      exists b. intuition.
      apply elem_of_list_further; eauto.
Qed.

(* TODO: upstream this *)
Section big_op.
Context `{Monoid M o}.
Implicit Types xs : list M.
Infix "`o`" := o (at level 50, left associativity).
Section gset.
  Context `{Countable A} `{Countable B}.
  Implicit Types X : gset A.
  Implicit Types f : A → M.

  Lemma set_map_union_singleton (h: A → B) X x:
    set_map h ({[x]} ∪ X) = ({[h x]} ∪ (set_map h X) : gset B).
  Proof. set_solver. Qed.

  Lemma big_opS_fmap (h: A → B) X (g: B → M):
    (∀ x y, h x = h y → x = y) →
    ([^o set] x ∈ set_map h X, g x) ≡ ([^o set] x ∈ X, g (h x)).
  Proof.
    intros Hinj.
    induction X as [|x X ? IH] using set_ind_L => //=; [ by rewrite big_opS_eq | ].
    rewrite set_map_union_singleton.
    rewrite ?big_opS_union.
    - rewrite ?big_opS_singleton IH //.
    - set_solver.
    - cut ((h x) ∉ (set_map h X : gset _)); first by set_solver.
      intros (x'&Heq&Hin)%elem_of_map.
      apply Hinj in Heq. subst. auto.
  Qed.
End gset.
End big_op.

Section bi_big_op.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.
Section map.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  Lemma big_sepM_mono_with_inv' P Φ Ψ m :
    (∀ k x, m !! k = Some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) →
    P ∗ ([∗ map] k ↦ x ∈ m, Φ k x) ⊢ P ∗ [∗ map] k ↦ x ∈ m, Ψ k x.
  Proof.
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

  Lemma map_filter_insert_not_strong:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A, Lookup K A (M A)) (H1 : ∀ A, Empty (M A))
    (H2 : ∀ A, PartialAlter K A (M A)) (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A, FinMapToList K A (M A))
    (EqDecision0 : EqDecision K),
    FinMap K M
    → ∀ A (P : K * A → Prop) (H7 : ∀ x : K * A, Decision (P x)) (m : M A) (i : K) (x : A),
       ¬ P (i, x) → filter P (<[i:=x]> m) = (filter P (delete i m)).
  Proof.
    intros. rewrite -insert_delete map_filter_insert_not' //= => ?.
    rewrite lookup_delete //=.
  Qed.

  Lemma big_sepM_filter Φ (R: K * A → Prop) {Hdec: ∀ k, Decision (R k)} m :
    ([∗ map] k ↦ x ∈ filter R m, Φ k x) ⊣⊢
    ([∗ map] k ↦ x ∈ m, if decide (R (k, x)) then Φ k x else emp).
  Proof.
    induction m as [|k v m ? IH] using map_ind.
    { by rewrite map_filter_empty !big_sepM_empty. }
    destruct (decide (R (k, v))).
    - rewrite map_filter_insert //.
      rewrite !big_sepM_insert //.
      * by rewrite decide_True // IH.
      * apply map_filter_lookup_None; eauto.
    - rewrite map_filter_insert_not' //; last by congruence.
      rewrite !big_sepM_insert // decide_False // IH. rewrite left_id. eauto.
  Qed.

  Lemma big_sepM_mono_with_inv P Φ Ψ m :
    (∀ k x, m !! k = Some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) →
    P -∗ ([∗ map] k ↦ x ∈ m, Φ k x) -∗ P ∗ [∗ map] k ↦ x ∈ m, Ψ k x.
  Proof.
    iIntros (?) "HP H". iApply (big_sepM_mono_with_inv' with "[HP H]"); eauto.
    iFrame.
  Qed.

  Lemma big_sepM_mono_with_pers (P: PROP) `{!BiAffine PROP} `{Persistent PROP P} Φ Ψ m :
    (∀ k x, m !! k = Some x → P -∗ Φ k x -∗ Ψ k x) →
    P -∗ ([∗ map] k ↦ x ∈ m, Φ k x) -∗ [∗ map] k ↦ x ∈ m, Ψ k x.
  Proof.
    iIntros (Himpl) "#HP H". iDestruct (big_sepM_mono_with_inv with "HP H") as "(_&$)"; eauto.
    iIntros (???) "(#HP&Φ)". iFrame "HP". by iApply Himpl.
  Qed.

  Lemma big_sepM_insert_delete Φ m i x :
    ([∗ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ Φ i x ∗ [∗ map] k↦y ∈ delete i m, Φ k y.
  Proof. rewrite -insert_delete big_sepM_insert ?lookup_delete //. Qed.

  Context `{BiAffine PROP}.
  Lemma big_sepM_mono_wand Φ Ψ m (I : PROP) :
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

  Context `{BiFUpd PROP}.
  Lemma big_sepM_mono_fupd Φ Ψ m (I : PROP) E :
   □ ( ∀ k x, ⌜ m !! k = Some x ⌝ -∗
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

End map.

Section list.

  Lemma big_sepL_drop {A} `{!BiAffine PROP} (Φ: nat → A → PROP) (m: list A) (n: nat):
    ([∗ list] k ↦ x ∈ m, Φ k x) ⊢ ([∗ list] k ↦ x ∈ drop n m, Φ (n + k) x).
  Proof.
    rewrite -{1}(take_drop n m) big_sepL_app take_length.
    iIntros "(_&H)".
    destruct (decide (length m ≤ n)).
    - rewrite drop_ge //=.
    - rewrite Nat.min_l //=; lia.
  Qed.

  Lemma big_sepL_mono_with_inv' {A} P Φ Ψ (m: list A) n :
    (∀ k x, m !! k = Some x → P ∗ Φ (k + n) x ⊢ P ∗ Ψ (k + n) x) →
    P ∗ ([∗ list] k ↦ x ∈ m, Φ (k + n) x) ⊢ P ∗ [∗ list] k ↦ x ∈ m, Ψ (k + n) x.
  Proof.
    revert n.
    induction m as [|a m] => n Hwand //=.
    - iIntros "(HP&HΦ&Hl)".
      iDestruct (Hwand 0 a with "[HP HΦ]") as "(HP&HΨ)"; eauto.
      { rewrite Nat.add_0_l. iFrame. }
      rewrite ?Nat.add_0_l.
      iFrame "HΨ".
      setoid_rewrite <-Nat.add_succ_r.
      iApply (IHm with "[$ ]"); eauto.
      intros; eauto.
      specialize (Hwand (S k)).
      rewrite Nat.add_succ_r -Nat.add_succ_l. iApply Hwand; eauto.
  Qed.

  Lemma big_sepL_mono_with_inv {A} P Φ Ψ (m: list A) :
    (∀ k x, m !! k = Some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) →
    P -∗ ([∗ list] k ↦ x ∈ m, Φ k x) -∗ P ∗ [∗ list] k ↦ x ∈ m, Ψ k x.
  Proof.
    iIntros (?) "HP H".
    iPoseProof (big_sepL_mono_with_inv' P Φ Ψ _ O with "[HP H]") as "H";
    setoid_rewrite Nat.add_0_r; eauto; iFrame.
  Qed.

  Lemma big_sepL_mono_with_pers {A} (P: PROP) `{!BiAffine PROP} `{Persistent PROP P} Φ Ψ (m: list A) :
    (∀ k x, m !! k = Some x → P -∗ Φ k x -∗ Ψ k x) →
    P -∗ ([∗ list] k ↦ x ∈ m, Φ k x) -∗ [∗ list] k ↦ x ∈ m, Ψ k x.
  Proof.
    iIntros (Himpl) "#HP H". iDestruct (big_sepL_mono_with_inv with "HP H") as "(_&$)"; eauto.
    iIntros (???) "(#HP&Φ)". iFrame "HP". by iApply Himpl.
  Qed.
End list.


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


Section map2.
  Context `{Countable K} {A B : Type}.
  Implicit Types Φ Ψ : K → A → B → PROP.

  Lemma big_sepM2_lookup_1_some
      Φ (m1 : gmap K A) (m2 : gmap K B) (i : K) (x1 : A)
      (_ : forall x2 : B, Absorbing (Φ i x1 x2)) :
    m1 !! i = Some x1 ->
      ⊢ ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
          ⌜∃ x2, m2 !! i = Some x2⌝.
  Proof.
    intros.
    iIntros "H".
    iDestruct (big_sepM2_lookup_1 with "H") as (x2) "[% _]"; eauto.
  Qed.

  Lemma big_sepM2_lookup_2_some
      Φ (m1 : gmap K A) (m2 : gmap K B) (i : K) (x2 : B)
      (_ : forall x1 : A, Absorbing (Φ i x1 x2)) :
    m2 !! i = Some x2 ->
      ⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
          ⌜∃ x1, m1 !! i = Some x1⌝.
  Proof.
    intros.
    iIntros "H".
    iDestruct (big_sepM2_lookup_2 with "H") as (x1) "[% _]"; eauto.
  Qed.

  Lemma big_sepM2_lookup_1_none
      Φ (m1 : gmap K A) (m2 : gmap K B) (i : K)
      (_ : forall (x1 : A) (x2 : B), Absorbing (Φ i x1 x2)) :
    m1 !! i = None ->
      ⊢ ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
          ⌜m2 !! i = None⌝.
  Proof.
    case_eq (m2 !! i); auto.
    iIntros (? ? ?) "H".
    iDestruct (big_sepM2_lookup_2 with "H") as (x2) "[% _]"; eauto; congruence.
  Qed.

  Lemma big_sepM2_lookup_2_none
      Φ (m1 : gmap K A) (m2 : gmap K B) (i : K)
      (_ : forall (x1 : A) (x2 : B), Absorbing (Φ i x1 x2)) :
    m2 !! i = None ->
      ⊢ ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
          ⌜m1 !! i = None⌝.
  Proof.
    case_eq (m1 !! i); auto.
    iIntros (? ? ?) "H".
    iDestruct (big_sepM2_lookup_1 with "H") as (x1) "[% _]"; eauto; congruence.
  Qed.

  Lemma big_sepM2_sepM_1
      Φ (m1 : gmap K A) (m2 : gmap K B)
      (_ : forall i x1 x2, Absorbing (Φ i x1 x2)) :
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
      ( [∗ map] k↦y1 ∈ m1, ∃ y2, ⌜ m2 !! k = Some y2 ⌝ ∗ Φ k y1 y2 ).
  Proof.
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
      iDestruct (big_sepM2_lookup_1_some with "H") as %H2.
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

  Lemma big_sepM2_sepM_2
      Φ (m1 : gmap K A) (m2 : gmap K B)
      (_ : forall i x1 x2, Absorbing (Φ i x1 x2)) :
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
      ( [∗ map] k↦y2 ∈ m2, ∃ y1, ⌜ m1 !! k = Some y1 ⌝ ∗ Φ k y1 y2 ).
  Proof.
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
      iDestruct (big_sepM2_lookup_2_some with "H") as %H2.
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

  Lemma big_sepM_sepM2 Φ (m1 : gmap K A)
      (_ : forall i x1 x2, Absorbing (Φ i x1 x2)) :
    ( [∗ map] k↦y1 ∈ m1, ∃ y2, Φ k y1 y2 ) -∗
    ∃ m2, ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ).
  Proof.
    iIntros "Hm".
    iInduction m1 as [|i x m] "IH" using map_ind.
    - iExists ∅. iApply big_sepM2_empty. done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      iDestruct "Hi" as (y2) "Hi".
      iDestruct ("IH" with "Hm") as (m2) "Hm".
      iExists (<[i := y2]> m2).
      iDestruct (big_sepM2_lookup_1_none with "Hm") as "%Hm2i"; eauto.
      iApply big_sepM2_insert; eauto.
      iFrame.
  Qed.

  Lemma big_sepM_sepM2_merge (Φ : K -> A -> PROP) (Ψ : K -> B -> PROP)
    (m1 : gmap K A) (m2 : gmap K B) :
    dom (gset K) m1 = dom (gset K) m2 ->
    ( [∗ map] k↦y1 ∈ m1, Φ k y1 ) ∗
    ( [∗ map] k↦y2 ∈ m2, Ψ k y2 ) -∗
    [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 ∗ Ψ k y2.
  Proof.
    iIntros (Hdom) "[Hm1 Hm2]".
    iInduction m1 as [|i x m] "IH" using map_ind forall (m2 Hdom).
    - rewrite dom_empty_L in Hdom. symmetry in Hdom. apply dom_empty_inv_L in Hdom.
      subst. iApply big_sepM2_empty. done.
    - destruct (m2 !! i) eqn:He.
      2: {
        apply (not_elem_of_dom (D:=gset K)) in He.
        rewrite -Hdom in He.
        exfalso. apply He.
        apply elem_of_dom. rewrite lookup_insert. eauto.
      }
      iDestruct (big_sepM_insert with "Hm1") as "[Hi1 Hm1]"; eauto.
      replace (m2) with (<[i:=b]> (delete i m2)).
      2: {
        rewrite insert_delete. rewrite insert_id; eauto.
      }
      iDestruct (big_sepM_insert with "Hm2") as "[Hi2 Hm2]"; eauto.
      { rewrite lookup_delete; eauto. }
      iApply big_sepM2_insert; eauto.
      { rewrite lookup_delete; eauto. }
      iFrame.
      iSpecialize ("IH" $! (delete i m2) _ with "Hm1 Hm2"). iApply "IH".
  Unshelve.
    rewrite dom_delete_L -Hdom dom_insert_L.
    assert (i ∉ dom (gset K) m).
    { apply not_elem_of_dom. eauto. }
    set_solver.
  Qed.

  Lemma big_sepM2_sepM_merge Φ (Ψ : K -> A -> PROP) (m1 : gmap K A) (m2 : gmap K B)
      (_ : forall i x1 x2, Absorbing (Φ i x1 x2)) :
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) ∗
    ( [∗ map] k↦y1 ∈ m1, Ψ k y1 ) -∗
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ∗ Ψ k y1 ).
  Proof.
    iIntros "[Hm2 Hm]".
    iInduction m1 as [|i x m] "IH" using map_ind forall (m2).
    - iDestruct (big_sepM2_empty_r with "Hm2") as "%He". subst. iApply big_sepM2_empty. done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      iDestruct (big_sepM2_lookup_1_some _ _ _ i with "Hm2") as (x2) "%Hm2i"; eauto.
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

  Theorem map_zip_empty_l (m2 : gmap K B) :
    map_zip (∅ : gmap K A) m2 = ∅.
  Proof.
    rewrite /map_zip.
    apply map_eq; intros.
    erewrite lookup_merge by reflexivity.
    repeat rewrite lookup_empty; eauto.
  Qed.

  Theorem map_zip_empty_r (m1 : gmap K A) :
    map_zip m1 (∅ : gmap K B) = ∅.
  Proof.
    rewrite /map_zip.
    apply map_eq; intros.
    erewrite lookup_merge by reflexivity.
    repeat rewrite lookup_empty; eauto.
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
      repeat rewrite lookup_insert. eauto.
    - erewrite lookup_merge by reflexivity.
      repeat rewrite lookup_insert_ne; eauto.
      erewrite lookup_merge by reflexivity.
      repeat rewrite lookup_insert_ne; eauto.
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
    - repeat rewrite map_filter_lookup_key_in; eauto.
      erewrite lookup_merge by reflexivity; eauto.
    - repeat rewrite map_filter_lookup_key_notin; eauto.
  Qed.

  Lemma big_sepM2_filter Φ (P : K -> Prop) (m1 : gmap K A) (m2 : gmap K B) 
                         `{! ∀ k, Decision (P k)} :
    ⊢
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) ∗-∗
    ( ( [∗ map] k↦y1;y2 ∈ filter (λ x, P x.1) m1;filter (λ x, P x.1) m2, Φ k y1 y2 ) ∗
      ( [∗ map] k↦y1;y2 ∈ filter (λ x, ¬P x.1) m1;filter (λ x, ¬P x.1) m2, Φ k y1 y2 ) ).
  Proof.
    rewrite big_sepM2_eq /big_sepM2_def.
    iSplit.
    - iIntros "[% Hm]".
      erewrite <- (map_union_filter _ (map_zip m1 m2)).
      iDestruct (big_sepM_union with "Hm") as "[Hmp Hmnp]".
      { eapply map_disjoint_filter. }
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
      { eapply map_disjoint_filter. }
      rewrite map_union_filter. iFrame.
  Unshelve.
    all: typeclasses eauto.
  Qed.

End map2.

Section list2.
  Context {A B : Type}.
  Implicit Types Φ Ψ : nat → A → B → PROP.

  Lemma big_sepL_merge_big_sepL2_aux (P: nat → A → PROP) (Q: nat → B → PROP) (l1: list A) (l2: list B) off:
    length l1 = length l2 →
    ([∗ list] k↦y1 ∈ l1, P (k + off) y1) -∗
    ([∗ list] k↦y2 ∈ l2, Q (k + off) y2) -∗
    ([∗ list] k↦y1;y2 ∈ l1;l2, P (k + off) y1 ∗ Q (k + off) y2).
  Proof.
    revert l2 off. induction l1; intros [|] off => /= Hlen; try congruence; eauto.
    iIntros "(HP&Hl1) (HQ&Hl2)".
    iFrame. setoid_rewrite <-Nat.add_succ_r.
    iApply (IHl1 with "[$] [$]"); eauto.
  Qed.

  (** XXX: shocked that this is not upstream? *)
  Lemma big_sepL_merge_big_sepL2 (P: nat → A → PROP) (Q: nat → B → PROP) (l1: list A) (l2: list B):
    length l1 = length l2 →
    ([∗ list] k↦y1 ∈ l1, P k y1) -∗
    ([∗ list] k↦y2 ∈ l2, Q k y2) -∗
    ([∗ list] k↦y1;y2 ∈ l1;l2, P k y1 ∗ Q k y2).
  Proof.
    intros. specialize (big_sepL_merge_big_sepL2_aux P Q l1 l2 O).
    setoid_rewrite Nat.add_0_r; eauto.
  Qed.

  Lemma big_sepL2_elim_big_sepL_aux `{!BiAffine PROP} {C} (P: nat → C → PROP) Φ (l1: list A) (l2: list B) (l: list C) n:
    length l = length l1 →
    □ (∀ k x y z, ⌜ l1 !! k = Some x ⌝ -∗
                  ⌜ l2 !! k = Some y ⌝ -∗
                  ⌜ l !! k = Some z ⌝ -∗ Φ (k + n) x y -∗ P (k + n) z) -∗
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ (k + n) y1 y2) -∗
    ([∗ list] k↦z ∈ l, P (k + n) z).
  Proof.
    intros Hlen1.  rewrite big_sepL2_alt.
    iIntros "#Halways (H&Hzip)". iDestruct "H" as %Hlen2.
    iInduction l as [|c l] "IH" forall (l1 l2 Hlen1 Hlen2 n);
    rewrite //=; destruct l1; destruct l2; simpl in Hlen1, Hlen2; try congruence; eauto.

    simpl. iDestruct "Hzip" as "(H&Hrest)".
    iDestruct ("Halways" $! 0 with "[] [] [] [H]") as "HP".
    { iPureIntro. simpl; eauto. }
    { iPureIntro. simpl; eauto. }
    { iPureIntro. simpl; eauto. }
    { rewrite Nat.add_0_l. iFrame. }
    rewrite Nat.add_0_l. iFrame.
    setoid_rewrite <-Nat.add_succ_r.
    unshelve (iSpecialize ("IH" $! l1 l2 _ _ (S n))); eauto.
    iApply "IH"; eauto.
    iAlways. iIntros (???? ???) "HΦ".
    setoid_rewrite Nat.add_succ_r.
    setoid_rewrite <-Nat.add_succ_l.
    iApply ("Halways" with "[] [] [] [$]"); eauto.
  Qed.

  Lemma big_sepL2_elim_big_sepL `{!BiAffine PROP} {C} (P: nat → C → PROP) Φ (l1: list A) (l2: list B) (l: list C):
    length l = length l1 →
    □ (∀ k x y z, ⌜ l1 !! k = Some x ⌝ -∗
                  ⌜ l2 !! k = Some y ⌝ -∗
                  ⌜ l !! k = Some z ⌝ -∗ Φ k x y -∗ P k z) -∗
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) -∗
    ([∗ list] k↦z ∈ l, P k z).
  Proof.
    iIntros (?) "H1 H2". iPoseProof (big_sepL2_elim_big_sepL_aux P Φ l1 l2 l O) as "H"; auto.
    setoid_rewrite Nat.add_0_r; eauto.
    iApply ("H" with "H1 H2"); eauto.
  Qed.

  Local Lemma big_sepL2_to_sepL_aux Φ n l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ (n+k) y1 y2) -∗
    ([∗ list] k↦y1 ∈ l1, ∃ y2, ⌜l2 !! k = Some y2⌝ ∗ Φ (n+k) y1 y2).
  Proof.
    iIntros "H".
    (iInduction l1 as [|y1 l1] "IH" forall (n l2)).
    - iDestruct (big_sepL2_length with "H") as %Hlen.
      assert (l2 = []).
      { apply length_zero_iff_nil; auto. }
      subst; simpl.
      auto.
    - iDestruct (big_sepL2_cons_inv_l with "H") as (y2 l2' ->) "(HΦ & H)".
      simpl.
      iSplitL "HΦ".
      { eauto with iFrame. }
      assert (forall k, n + S k = S n + k) as Harith by lia.
      setoid_rewrite Harith.
      iApply ("IH" with "H").
  Qed.

  Lemma big_sepL2_to_sepL_1 Φ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) -∗
    ([∗ list] k↦y1 ∈ l1, ∃ y2, ⌜l2 !! k = Some y2⌝ ∗ Φ k y1 y2).
  Proof.
    iApply (big_sepL2_to_sepL_aux Φ O).
  Qed.

  Lemma big_sepL2_mono_with_pers (P: PROP) `{!BiAffine PROP} `{Persistent PROP P} (Φ Ψ: nat → A → B → PROP) l1 l2:
    (∀ k x y, l1 !! k = Some x → l2 !! k = Some y → P -∗ Φ k x y -∗ Ψ k x y) →
    P -∗ ([∗ list] k ↦ x;y ∈ l1;l2, Φ k x y) -∗ [∗ list] k ↦ x;y ∈ l1;l2, Ψ k x y.
  Proof.
    iIntros (Himpl) "HP".
    rewrite ?big_sepL2_alt.
    iIntros "(%&Hwand)". iSplit; first auto.
    iApply (big_sepL_mono_with_pers P (λ k ab, Φ k (fst ab) (snd ab))
                                      (λ k ab, Ψ k (fst ab) (snd ab)) with "HP Hwand").
    { intros k x Hlookup. eapply Himpl; eauto.
      - rewrite -(fst_zip l1 l2); last lia.
        rewrite list_lookup_fmap Hlookup //=.
      - rewrite -(snd_zip l1 l2); last lia.
        rewrite list_lookup_fmap Hlookup //=.
    }
  Qed.

  Lemma big_sepL2_lookup_1_some
      Φ (l1 : list A) (l2 : list B) (i : nat) (x1 : A) :
    l1 !! i = Some x1 ->
      ⊢ ( [∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ) -∗
          ⌜∃ x2, l2 !! i = Some x2⌝.
  Proof.
    intros.
    iIntros "H".
    apply lookup_lt_Some in H as Hlen.
    iDestruct (big_sepL2_length with "H") as %Hslen.
    rewrite Hslen in Hlen.
    apply lookup_lt_is_Some_2 in Hlen.
    destruct Hlen.
    eauto.
  Qed.

  Lemma big_sepL2_lookup_2_some
      Φ (l1 : list A) (l2 : list B) (i : nat) (x2 : B) :
    l2 !! i = Some x2 ->
      ⊢ ( [∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ) -∗
          ⌜∃ x1, l1 !! i = Some x1⌝.
  Proof.
    intros.
    iIntros "H".
    apply lookup_lt_Some in H as Hlen.
    iDestruct (big_sepL2_length with "H") as %Hslen.
    rewrite -Hslen in Hlen.
    apply lookup_lt_is_Some_2 in Hlen.
    destruct Hlen.
    eauto.
  Qed.

  Lemma big_sepL2_lookup_1_none
      Φ (l1 : list A) (l2 : list B) (i : nat) :
    l1 !! i = None ->
      ⊢ ( [∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ) -∗
          ⌜l2 !! i = None⌝.
  Proof.
    intros.
    iIntros "H".
    apply lookup_ge_None in H as Hlen.
    iDestruct (big_sepL2_length with "H") as %Hslen.
    rewrite Hslen in Hlen.
    apply lookup_ge_None in Hlen.
    eauto.
  Qed.

  Lemma big_sepL2_lookup_2_none
      Φ (l1 : list A) (l2 : list B) (i : nat) :
    l2 !! i = None ->
      ⊢ ( [∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ) -∗
          ⌜l1 !! i = None⌝.
  Proof.
    intros.
    iIntros "H".
    apply lookup_ge_None in H as Hlen.
    iDestruct (big_sepL2_length with "H") as %Hslen.
    rewrite -Hslen in Hlen.
    apply lookup_ge_None in Hlen.
    eauto.
  Qed.

End list2.

(* needs to be outside the section since it changes the context type
parameters *)
Lemma big_sepL2_to_sepL_2 {A B} (Φ: nat → A → B → PROP) l1 l2 :
  ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) -∗
  ([∗ list] k↦y2 ∈ l2, ∃ y1, ⌜l1 !! k = Some y1⌝ ∗ Φ k y1 y2).
Proof.
  iIntros "H".
  iApply big_sepL2_to_sepL_1.
  iApply big_sepL2_flip; auto.
Qed.

Section maplist.
  Context `{Countable K} {V LV : Type}.
  Implicit Types Φ Ψ : K → V → LV → PROP.
  Implicit Types m : gmap K V.
  Implicit Types l : list LV.

  Definition big_sepML_def Φ m l : PROP :=
    (∃ lm,
      ⌜ l ≡ₚ snd <$> (map_to_list lm) ⌝ ∗
      [∗ map] k ↦ v;lvm ∈ m;lm, Φ k v lvm)%I.
  Definition big_sepML_aux : seal (@big_sepML_def). Proof. by eexists. Qed.
  Definition big_sepML := unseal big_sepML_aux.
  Definition big_sepML_eq : @big_sepML = @big_sepML_def := big_sepML_aux.(seal_eq).

  Global Instance big_sepML_proper :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊢)))
       ==> (=) ==> (Permutation) ==> (⊢))
           (big_sepML).
  Proof.
    intros P0 P1 HP.
    intros m0 m Hm; subst.
    intros l0 l1 Hl.
    rewrite big_sepML_eq.
    iIntros "Hml".
    iDestruct "Hml" as (lm) "[Hlm Hml]".
    rewrite Hl.
    iExists lm; iFrame.
    iSplitR; first done.
    iApply big_sepM2_mono; iFrame.
    iIntros (k v lv ? ?) "H".
    iApply HP; iFrame.
  Qed.

  Theorem big_sepML_empty Φ `{!∀ k v lv, Absorbing (Φ k v lv)} :
    ⊢ big_sepML Φ ∅ nil.
  Proof.
    iIntros.
    rewrite big_sepML_eq.
    iExists ∅.
    iSplit; eauto.
    iApply big_sepM2_empty. done.
  Qed.

  Theorem big_sepML_insert Φ m l k v lv `{!∀ k v lv, Absorbing (Φ k v lv)} :
    m !! k = None ->
    Φ k v lv ∗ big_sepML Φ m l -∗
    big_sepML Φ (<[k := v]> m) (lv :: l).
  Proof.
    iIntros "% [Hp Hml]".
    rewrite big_sepML_eq.
    iDestruct "Hml" as (lm) "[% Hml]".
    iDestruct (big_sepM2_lookup_1_none with "Hml") as %Hlmnone; eauto.
    iExists (<[k := lv]> lm).
    iSplitR.
    - iPureIntro.
      rewrite map_to_list_insert; eauto.
      rewrite /=.
      rewrite H2.
      reflexivity.
    - iApply big_sepM2_insert; eauto.
      iFrame.
  Qed.

  Theorem big_sepML_insert_app Φ m l k v lv `{!∀ k v lv, Absorbing (Φ k v lv)} :
    m !! k = None ->
    Φ k v lv ∗ big_sepML Φ m l -∗
    big_sepML Φ (<[k := v]> m) (l ++ [lv]).
  Proof.
    iIntros "% [Hp Hml]".
    rewrite -Permutation_cons_append.
    iApply big_sepML_insert; eauto; iFrame.
  Qed.

  Theorem big_sepML_delete_cons Φ m l lv `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ m (lv :: l) -∗
    ∃ k v,
      ⌜ m !! k = Some v ⌝ ∗
      Φ k v lv ∗
      big_sepML Φ (delete k m) l.
  Proof.
    iIntros "Hml".
    rewrite big_sepML_eq.
    iDestruct "Hml" as (lm) "[% Hml]".
    assert (lv ∈ lv :: l) by apply elem_of_list_here.
    setoid_rewrite H1 in H2.
    apply elem_of_map_list in H2. destruct H2 as [[k lv0] H2].
    simpl in H2; intuition subst.
    apply elem_of_map_to_list in H3.
    iDestruct (big_sepM2_lookup_2_some with "Hml") as %[v Hmk]; eauto.
    iExists _, _.
    iSplitR; eauto.
    iDestruct (big_sepM2_delete with "Hml") as "[Hp Hml]"; eauto.
    iFrame.
    iExists _.
    iSplitR; last iFrame.
    iPureIntro.
    replace lm with (<[k := lv]> (delete k lm)) in H1.
    2: {
      rewrite insert_delete.
      rewrite insert_id; eauto.
    }
    setoid_rewrite map_to_list_insert in H1.
    2: apply lookup_delete.
    simpl in H1.
    apply Permutation.Permutation_cons_inv in H1.
    done.
  Qed.

  Lemma map_to_list_insert_overwrite (l : list LV) (i : nat) (k : K) (lv lv' : LV) (lm : gmap K LV) :
    l !! i = Some lv ->
    lm !! k = Some lv ->
    l ≡ₚ (map_to_list lm).*2 ->
    <[i := lv']> l ≡ₚ (map_to_list (<[k := lv']> lm)).*2.
  Proof.
    intros.
    rewrite -insert_delete.
    rewrite map_to_list_insert.
    2: apply lookup_delete.

    erewrite delete_Permutation in H2; eauto.
    erewrite (delete_Permutation _ i lv').
    2: { rewrite list_lookup_insert; eauto.
         eapply lookup_lt_Some; eauto. }
    erewrite <- (insert_id lm) in H2; eauto.
    rewrite -insert_delete in H2.
    erewrite map_to_list_insert in H2.
    2: apply lookup_delete.
    simpl in *.
    apply Permutation.Permutation_cons_inv in H2.
    rewrite -H2.
    eapply Permutation_cons.
    repeat rewrite delete_take_drop.
    rewrite -> take_insert by lia.
    rewrite -> drop_insert_gt by lia.
    eauto.
  Qed.

  Lemma map_to_list_delete (l : list LV) (lm : gmap K LV) (k : K) (i : nat) (x : LV) :
    l !! i = Some x ->
    lm !! k = Some x ->
    l ≡ₚ (map_to_list lm).*2 ->
    delete i l ≡ₚ (map_to_list (delete k lm)).*2.
  Proof.
    intros.
    erewrite delete_Permutation in H2; eauto.
    erewrite <- (insert_id lm) in H2; eauto.
    rewrite -insert_delete in H2.
    erewrite map_to_list_insert in H2.
    2: apply lookup_delete.
    simpl in *.
    apply Permutation.Permutation_cons_inv in H2.
    eauto.
  Qed.

  Theorem big_sepML_delete_m Φ m l k v `{!∀ k v lv, Absorbing (Φ k v lv)} :
    m !! k = Some v ->
    big_sepML Φ m l -∗
    ∃ i lv,
      ⌜ l !! i = Some lv ⌝ ∗
      Φ k v lv ∗
      big_sepML Φ (delete k m) (delete i l).
  Proof.
    iIntros (Hm) "Hml".
    rewrite big_sepML_eq.
    iDestruct "Hml" as (lm) "[% Hml]".
    iDestruct (big_sepM2_lookup_1_some with "Hml") as (x2) "%"; eauto.
    iDestruct (big_sepM2_delete with "Hml") as "[Hk Hml]"; eauto.

    apply elem_of_map_to_list in H2 as H2'.
    eapply (elem_of_list_fmap_1 snd) in H2'.
    rewrite <- H1 in H2'.
    eapply elem_of_list_lookup_1 in H2'.
    destruct H2'.

    iExists _, _; iFrame.
    iSplitR; eauto.

    iExists _; iFrame.
    iPureIntro.
    eapply map_to_list_delete; eauto.
  Qed.

  Lemma list_some_map_to_list (l : list LV) (i : nat) (lv : LV) (lm : gmap K LV) :
    l !! i = Some lv ->
    l ≡ₚ (map_to_list lm).*2 ->
    ∃ k,
      lm !! k = Some lv.
  Proof.
    intros.
    assert (lv ∈ l). { eapply elem_of_list_lookup_2; eauto. }
    rewrite -> H1 in H2.
    eapply elem_of_list_fmap_2 in H2.
    destruct H2. intuition subst.
    destruct x.
    apply elem_of_map_to_list in H4.
    eexists. eauto.
  Qed.

  Lemma map_to_list_some_list (l : list LV) (k : K) (lv : LV) (lm : gmap K LV) :
    lm !! k = Some lv ->
    l ≡ₚ (map_to_list lm).*2 ->
    ∃ (i : nat),
      l !! i = Some lv.
  Proof.
    intros.
    apply elem_of_map_to_list in H0.
    eapply elem_of_list_fmap_1 in H0.
    erewrite <- H1 in H0.
    eapply elem_of_list_lookup_1 in H0.
    eauto.
  Qed.

  Theorem big_sepML_lookup_l_acc Φ m l i lv `{!∀ k v lv, Absorbing (Φ k v lv)} :
    l !! i = Some lv ->
    big_sepML Φ m l -∗
    ∃ k v, ⌜ m !! k = Some v ⌝ ∗ Φ k v lv ∗
    ∀ v' lv',
      Φ k v' lv' -∗
      big_sepML Φ (<[k := v']> m) (<[i := lv']> l).
  Proof.
    iIntros (Hi) "Hml".
    rewrite big_sepML_eq /big_sepML_def.
    iDestruct "Hml" as (lm) "[% Hml]".
    eapply list_some_map_to_list in Hi as Hi'; eauto. destruct Hi'.
    iDestruct (big_sepM2_lookup_2_some with "Hml") as (xm) "%"; eauto.
    iDestruct (big_sepM2_insert_acc with "Hml") as "[Hx Hml]"; eauto.
    iExists _, _.
    iSplitR; first by done.
    iFrame.
    iIntros (??) "Hx".
    iSpecialize ("Hml" with "Hx").
    iExists (<[x := a0]> lm). iFrame.
    iPureIntro.
    eapply map_to_list_insert_overwrite; eauto.
  Qed.

  Theorem big_sepML_lookup_l_app_acc Φ m lv l0 l1 `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ m (l0 ++ lv :: l1) -∗
    ∃ k v, ⌜ m !! k = Some v ⌝ ∗ Φ k v lv ∗
    ∀ v' lv',
      Φ k v' lv' -∗
      big_sepML Φ (<[k := v']> m) (l0 ++ lv' :: l1).
  Proof.
    iIntros "Hml".
    iDestruct (big_sepML_lookup_l_acc with "Hml") as "Hres".
    { rewrite lookup_app_r. erewrite Nat.sub_diag. eauto. lia. }
    iDestruct "Hres" as (k v) "(% & Hk & Hml)".
    iExists _, _.
    iSplitR; first eauto.
    iFrame.
    iIntros (v' lv') "Hk".
    iSpecialize ("Hml" with "Hk").
    replace (length l0) with (length l0 + 0) by lia.
    rewrite insert_app_r. simpl. iFrame.
  Qed.

  Theorem big_sepML_lookup_m_acc Φ m l k v `{!∀ k v lv, Absorbing (Φ k v lv)} :
    m !! k = Some v ->
    big_sepML Φ m l -∗
    ∃ i lv, ⌜ l !! i = Some lv ⌝ ∗ Φ k v lv ∗
    ∀ v' lv',
      Φ k v' lv' -∗
      big_sepML Φ (<[k := v']> m) (<[i := lv']> l).
  Proof.
    iIntros (Hi) "Hml".
    rewrite big_sepML_eq /big_sepML_def.
    iDestruct "Hml" as (lm) "[% Hml]".
    iDestruct (big_sepM2_lookup_1_some with "Hml") as (xm) "%"; eauto.
    iDestruct (big_sepM2_insert_acc with "Hml") as "[Hx Hml]"; eauto.
    eapply map_to_list_some_list in H2 as H2'; eauto. destruct H2'.
    iExists _, _.
    iSplitR; first by done.
    iFrame.
    iIntros (??) "Hx".
    iSpecialize ("Hml" with "Hx").
    iExists (<[k := a0]> lm). iFrame.
    iPureIntro.
    eapply map_to_list_insert_overwrite; eauto.
  Qed.

  Theorem big_sepML_mono Φ Ψ m l `{!∀ k v lv, Absorbing (Φ k v lv)} `{!∀ k v lv, Absorbing (Ψ k v lv)} :
    big_sepML Φ m l -∗
    ⌜ ∀ k v lv, Φ k v lv -∗ Ψ k v lv ⌝ -∗
    big_sepML Ψ m l.
  Proof.
    rewrite big_sepML_eq; iIntros "Hml %".
    iDestruct "Hml" as (lm) "[% Hml]".
    iExists lm; iSplitR; first by eauto.
    iApply big_sepM2_mono; eauto.
  Qed.

  Theorem big_sepML_lookup_l_Some Φ m l i lv `{!∀ k v lv, Absorbing (Φ k v lv)} :
    l !! i = Some lv ->
    big_sepML Φ m l -∗
    ⌜ ∃ k v, m !! k = Some v ⌝.
  Proof.
    iIntros (Hl) "Hml".
    iDestruct (big_sepML_lookup_l_acc with "Hml") as (k v) "[% Hml]"; eauto.
  Qed.

  Theorem big_sepML_lookup_m_Some Φ m l k v `{!∀ k v lv, Absorbing (Φ k v lv)} :
    m !! k = Some v ->
    big_sepML Φ m l -∗
    ⌜ ∃ i lv, l !! i = Some lv ⌝.
  Proof.
    iIntros (Hm) "Hml".
    iDestruct (big_sepML_lookup_m_acc with "Hml") as (i lv) "[% Hml]"; eauto.
  Qed.

  Theorem big_sepML_empty_m Φ m `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ m [] -∗
    ⌜ m = ∅ ⌝.
  Proof.
    rewrite big_sepML_eq /big_sepML_def.
    iIntros "Hml".
    iDestruct "Hml" as (lm) "[% Hml]".
    destruct (map_to_list lm) eqn:Heq.
    - apply map_to_list_empty_inv in Heq; subst.
      iDestruct (big_sepM2_empty_l with "Hml") as %He. done.
    - simpl in *. apply Permutation_nil_cons in H1. eauto.
  Qed.

  Theorem big_sepML_empty_l Φ l `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ ∅ l -∗
    ⌜ l = [] ⌝.
  Proof.
    rewrite big_sepML_eq /big_sepML_def.
    iIntros "Hml".
    iDestruct "Hml" as (lm) "[% Hml]".
    iDestruct (big_sepM2_empty_r with "Hml") as %He; subst.
    rewrite map_to_list_empty /= in H1.
    iPureIntro. eapply Permutation.Permutation_nil. done.
  Qed.

  Theorem big_sepML_sep Φ Ψ m l :
    big_sepML (λ k v lv, Φ k v lv ∗ Ψ k v lv) m l -∗
    big_sepML Φ m l ∗ big_sepML Ψ m l.
  Proof.
    iIntros "Hml".
    rewrite big_sepML_eq.
    iDestruct "Hml" as (lm) "[% Hml]".
    iDestruct (big_sepM2_sep with "Hml") as "[Hml0 Hml1]".
    iSplitL "Hml0".
    { iExists _. iFrame. done. }
    { iExists _. iFrame. done. }
  Qed.

  Context `{BiAffine PROP}.
  Theorem big_sepML_sepM Φ (P : K -> V -> PROP) m l `{!∀ k v, Absorbing (P k v)}:
    big_sepML (λ k v lv, Φ k v lv ∗ P k v) m l ⊣⊢
    big_sepML Φ m l ∗ big_opM _ P m.
  Proof.
    rewrite big_sepML_eq; iSplit.
    - iIntros "Hlm".
      iDestruct "Hlm" as (lm) "[% Hlm]".
      iDestruct (big_sepM2_sep with "Hlm") as "[Hlm0 Hlm1]".
      iSplitL "Hlm0".
      + iExists _. iFrame. done.
      + iDestruct (big_sepM2_sepM_1 with "Hlm1") as "Hlm1".
        iDestruct (big_sepM_mono with "Hlm1") as "Hlm1"; last by iFrame.
        iIntros (k x Hkx) "H".
        iDestruct "H" as (y2) "[% H]". iFrame.
    - iIntros "[Hlm Hm]".
      iDestruct "Hlm" as (lm) "[% Hlm]".
      iExists _. iSplitR; first by eauto.
      iDestruct (big_sepM2_dom with "Hlm") as "%Hmlm".
      iApply big_sepM2_sep; iFrame.
      rewrite big_sepM2_eq /big_sepM2_def.
      iSplit.
      { iPureIntro. split; intros.
        { apply (elem_of_dom (D:=gset K)). rewrite -Hmlm. apply elem_of_dom. eauto. }
        { apply (elem_of_dom (D:=gset K)). rewrite Hmlm. apply elem_of_dom. eauto. }
      }
      clear H2.
      iInduction m as [|i x m] "IH" using map_ind forall (lm Hmlm).
      { rewrite dom_empty_L in Hmlm. rewrite (dom_empty_inv_L (D:=gset K) lm); eauto.
        rewrite map_zip_empty_l. iApply big_sepM_empty. done. }
      iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      assert (is_Some (lm !! i)) as Hlmi.
      { apply (elem_of_dom (D:=gset K)). rewrite -Hmlm. apply elem_of_dom. rewrite lookup_insert; eauto. }
      destruct Hlmi.
      replace lm with (<[i:=x0]> (delete i lm)).
      2: { rewrite insert_delete insert_id; eauto. }
      rewrite map_zip_insert.
      iApply big_sepM_insert.
      { rewrite map_zip_lookup_none_1; eauto. }
      iFrame.
      iApply "IH"; last by iFrame.
      iPureIntro.
      rewrite dom_delete_L -Hmlm dom_insert_L.
      assert (i ∉ dom (gset K) m).
      { apply not_elem_of_dom. eauto. }
      set_solver.
  Qed.

  Theorem big_sepML_sepL_split Φ (P : LV -> PROP) m l `{!∀ lv, Absorbing (P lv)}:
    big_sepML (λ k v lv, Φ k v lv ∗ P lv) m l -∗
    big_sepML Φ m l ∗ big_opL _ (λ i, P) l.
  Proof.
    rewrite big_sepML_eq.
    iIntros "Hlm".
    iDestruct "Hlm" as (lm) "[% Hlm]".
    iDestruct (big_sepM2_sep with "Hlm") as "[Hlm0 Hlm1]".
    iSplitL "Hlm0".
    + iExists _. iFrame. done.
    + iDestruct (big_sepM2_sepM_2 with "Hlm1") as "Hlm1".
      rewrite big_opM_eq /big_opM_def H2 big_sepL_fmap.
      iApply big_sepL_mono; last by iFrame.
      iIntros (???) "H".
      destruct y.
      iDestruct "H" as (?) "[% H]". iFrame.
  Qed.

  Theorem big_sepML_sepL_combine Φ (P : LV -> PROP) m l `{!∀ lv, Absorbing (P lv)}:
    big_sepML Φ m l ∗ big_opL _ (λ i, P) l -∗
    big_sepML (λ k v lv, Φ k v lv ∗ P lv) m l.
  Proof.
    rewrite big_sepML_eq.
    iIntros "Hlm".
    iDestruct "Hlm" as "[Hlm Hl]".
    iDestruct "Hlm" as (lm) "[% Hlm]".
    iExists _. iSplitR; first by eauto.
    rewrite big_sepM2_eq /big_sepM2_def.
    iDestruct "Hlm" as "[% Hlm]".
    iSplit; eauto.
    rewrite H2.
    iApply big_sepM_sep; iFrame.

    clear H2.
    iInduction lm as [|i x lm] "IH" using map_ind forall (m H3).
    { rewrite map_zip_empty_r. iApply big_sepM_empty. done. }
    rewrite map_to_list_insert; eauto.
    rewrite fmap_cons /=.
    iDestruct "Hl" as "[Hx Hl]".
    assert (is_Some (m !! i)) as Hmi.
    { apply H3. rewrite lookup_insert. eauto. }
    destruct Hmi.
    replace m with (<[i:=x0]> (delete i m)).
    2: { rewrite insert_delete insert_id; eauto. }
    rewrite map_zip_insert.
    iApply big_sepM_insert.
    { rewrite map_zip_lookup_none_2; eauto. }
    iFrame.
    iApply "IH"; last by iFrame.

    iPureIntro.
    split; intros.
    - destruct (decide (i = k)); subst.
      + rewrite lookup_delete in H5. inversion H5. congruence.
      + rewrite lookup_delete_ne in H5; eauto.
        apply H3 in H5. rewrite lookup_insert_ne in H5; eauto.
    - destruct (decide (i = k)); subst.
      + inversion H5. congruence.
      + rewrite lookup_delete_ne; eauto.
        eapply H3. rewrite lookup_insert_ne; eauto.
  Qed.

  Theorem big_sepML_sepL Φ (P : LV -> PROP) m l `{!∀ lv, Absorbing (P lv)}:
    big_sepML (λ k v lv, Φ k v lv ∗ P lv) m l ⊣⊢
    big_sepML Φ m l ∗ big_opL _ (λ i, P) l.
  Proof.
    iSplit.
    - iApply big_sepML_sepL_split.
    - iApply big_sepML_sepL_combine.
  Qed.

  Theorem big_sepML_sepL_exists Φ m l `{!∀ k v lv, Absorbing (Φ k v lv)}:
    big_sepML Φ m l -∗
    big_opL _ (λ _ lv, ∃ k v, ⌜ m !! k = Some v ⌝ ∗ Φ k v lv) l.
  Proof.
    rewrite big_sepML_eq /big_sepML_def.
    iIntros "Hml".
    iDestruct "Hml" as (lm) "[%Hllm Hml]".
    iDestruct (big_sepM2_sepM_2 with "Hml") as "Hlm".

    rewrite Hllm; clear Hllm.
    iInduction lm as [|i x lm] "IH" using map_ind.
    { rewrite map_to_list_empty. done. }
    iDestruct (big_sepM_insert with "Hlm") as "[Hi Hlm]"; eauto.
    rewrite map_to_list_insert; eauto.
    rewrite fmap_cons /=.
    iSplitL "Hi".
    { iExists _. iFrame. }
    iApply "IH". iFrame.
  Qed.

  Global Instance big_sepML_persistent `(!∀ k v lv, Persistent (Φ k v lv)) :
    Persistent (big_sepML Φ m l).
  Proof.
    rewrite big_sepML_eq.
    typeclasses eauto.
  Qed.

  Global Instance big_sepML_absorbing `(!∀ k v lv, Absorbing (Φ k v lv)) :
    Absorbing (big_sepML Φ m l).
  Proof.
    rewrite big_sepML_eq.
    typeclasses eauto.
  Qed.

End maplist.

Section maplist2.
  Context `{Countable K} {V W LV : Type}.
  Implicit Types Φ : K → V → LV → PROP.
  Implicit Types v : V.
  Implicit Types w : W.
  Implicit Types mv : gmap K V.
  Implicit Types mw : gmap K W.
  Implicit Types l : list LV.

  Context `{BiAffine PROP}.

  Theorem big_sepML_map_val_exists_helper Φ mv l (R : K -> V -> W -> Prop)
      `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ mv l -∗
    □ ( ∀ k v lv,
      ⌜ mv !! k = Some v ⌝ -∗
      Φ k v lv -∗
      ⌜ ∃ w, R k v w ⌝ ) -∗
    ∃ mw,
      ⌜ dom (gset K) mw = dom (gset K) mv ⌝ ∗
      big_sepML (λ k w lv, ∃ v, ⌜ R k v w ⌝ ∗ Φ k v lv) mw l.
  Proof.
    iIntros "Hml HR".
    iInduction l as [|] "Hi" forall (mv).
    - iExists ∅.
      iDestruct (big_sepML_empty_m with "Hml") as "->".
      iSplit; last by iApply big_sepML_empty.
      repeat rewrite dom_empty_L; eauto.
    - iDestruct (big_sepML_delete_cons with "Hml") as (k v) "(% & Hk & Hml)".
      iDestruct "HR" as "#HR".
      iSpecialize ("Hi" with "Hml [HR]").
      { iModIntro.
        iIntros. iApply "HR"; last by iFrame.
        apply lookup_delete_Some in a0; intuition eauto. }
      iDestruct "Hi" as (mw) "[% Hi]".
      iDestruct ("HR" with "[] Hk") as (w) "%HR"; eauto.
      iExists (<[k := w]> mw).
      iSplitR.
      { iPureIntro. rewrite dom_insert_L H3 dom_delete_L.
        assert (k ∈ dom (gset K) mv).
        { apply elem_of_dom; eauto. }
        rewrite -union_difference_L; eauto.
        set_solver.
      }
      iDestruct (big_sepML_insert with "[$Hi Hk]") as "Hml".
      2: { iExists _. iFrame. done. }
      2: iFrame.
      apply (not_elem_of_dom (D:=gset K)). rewrite H3. set_solver.
  Qed.

  Theorem big_sepML_map_val_exists Φ mv l (R : K -> V -> W -> Prop)
      `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ mv l -∗
    □ ( ∀ k v lv,
      ⌜ mv !! k = Some v ⌝ -∗
      Φ k v lv -∗
      ⌜ ∃ w, R k v w ⌝ ) -∗
    ∃ mw,
      big_sepML (λ k w lv, ∃ v, ⌜ R k v w ⌝ ∗ Φ k v lv) mw l.
  Proof.
    iIntros "Hml HR".
    iDestruct (big_sepML_map_val_exists_helper with "Hml HR") as (mw) "[% H]".
    iExists _; iFrame.
  Qed.

  Theorem big_sepML_exists (Φw : K -> V -> LV -> W -> PROP) m l
      `{!∀ k v lv w, Absorbing (Φw k v lv w)} :
    big_sepML (λ k v lv, ∃ w, Φw k v lv w) m l -∗
    ∃ lw,
      ⌜ l = fst <$> lw ⌝ ∗
      big_sepML (λ k v lv, Φw k v (fst lv) (snd lv)) m lw.
  Proof.
    iIntros "Hml".
    iInduction l as [|] "Hi" forall (m).
    - iExists nil.
      iDestruct (big_sepML_empty_m with "Hml") as "->".
      iSplitR; first by done.
      iApply big_sepML_empty.
    - iDestruct (big_sepML_delete_cons with "Hml") as (k v) "(% & Hk & Hml)".
      iDestruct "Hk" as (w) "Hk".
      iSpecialize ("Hi" with "Hml").
      iDestruct "Hi" as (lw) "(% & Hi)".
      iExists ((a, w) :: lw).
      iSplitR; first by subst; eauto.
      replace m with (<[k := v]> (delete k m)) at 2.
      2: { rewrite insert_delete. rewrite insert_id; eauto. }
      iApply big_sepML_insert.
      { rewrite lookup_delete; eauto. }
      iFrame.
  Qed.

End maplist2.

Theorem big_sepL_impl A (f g: nat -> A -> PROP) (l: list A) :
  (forall i x, f i x -∗ g i x) ->
  ([∗ list] i↦x ∈ l, f i x) -∗
  ([∗ list] i↦x ∈ l, g i x).
Proof.
  intros Himpl.
  apply big_opL_gen_proper; auto.
  typeclasses eauto.
Qed.

Definition Conflicting {L V} (P0 P1 : L -> V -> PROP) :=
  ∀ a0 v0 a1 v1,
    P0 a0 v0 -∗ P1 a1 v1 -∗ ⌜ a0 ≠ a1 ⌝.

Lemma big_sepM_disjoint_pred {L V} {P0 P1 : L -> V -> PROP} `{!EqDecision L} `{!Countable L}
  `{!∀ l v, Absorbing (P0 l v)}
  `{!∀ l v, Absorbing (P1 l v)}
  `(Conflicting P0 P1)
  (m0 m1 : gmap L V) :
  ( ( [∗ map] a↦v ∈ m0, P0 a v ) -∗
    ( [∗ map] a↦v ∈ m1, P1 a v ) -∗
    ⌜ m0 ##ₘ m1 ⌝ ).
Proof.
  iIntros "H0 H1".
  iIntros (i).
  unfold option_relation.
  destruct (m0 !! i) eqn:He; destruct (m1 !! i) eqn:H1; try solve [ iPureIntro; auto ].
  iDestruct (big_sepM_lookup with "H0") as "H0"; eauto.
  iDestruct (big_sepM_lookup with "H1") as "H1"; eauto.
  iDestruct (Conflicting0 with "H0 H1") as %Hcc.
  congruence.
Qed.

End bi_big_op.

Notation "'[∗' 'maplist]' k ↦ x ; v ∈ m ; l , P" :=
  (big_sepML (λ k x v, P) m l)
  (at level 200, m, l at level 10, k, x, v at level 1, right associativity,
   format "[∗  maplist]  k ↦ x ; v  ∈  m ; l ,  P")
  : bi_scope.

Opaque big_sepML.

(** * additional instances for big_sepM *)
Instance big_sepM_IntoPure {PROP: bi} `{Countable K} {V}
        (Φ: K → V → PROP) (P: K → V → Prop)
        {ΦP: ∀ k v, IntoPure (Φ k v) (P k v)}
        (m: gmap K V) :
  IntoPure ([∗ map] k↦x ∈ m, Φ k x) (map_Forall P m).
Proof.
  induction m using map_ind; simpl.
  - hnf; iIntros "_ !%".
    apply map_Forall_empty.
  - hnf; iIntros "HP".
    rewrite -> big_sepM_insert by auto.
    iDestruct (into_pure with "HP") as %?.
    iPureIntro.
    rewrite -> map_Forall_insert by auto.
    auto.
Qed.

Lemma big_sepM_from_Forall {PROP: bi} `{Countable K} {V}
      (Φ: K → V → PROP) (P: K → V → Prop)
      (m: gmap K V) :
  (∀ k v, P k v → ⊢ Φ k v) →
  map_Forall P m →
  ⊢ [∗ map] k↦x ∈ m, Φ k x.
Proof.
  intros HfromP.
  induction m using map_ind; simpl; intros.
  - iApply big_sepM_empty; auto.
  - rewrite -> big_sepM_insert by auto.
    rewrite -> map_Forall_insert in H1 by auto.
    intuition.
    iSplitL.
    + iApply HfromP; auto.
    + auto.
Qed.

Instance big_sepM_FromPure_affine {PROP: bi} `{Countable K} {V}
          (Φ: K → V → PROP) (P: K → V → Prop)
          {ΦP: ∀ k v, FromPure true (Φ k v) (P k v)}
          (m: gmap K V) :
  FromPure true ([∗ map] k↦x ∈ m, Φ k x) (map_Forall P m).
Proof.
  hnf; simpl.
  iIntros "%".
  iApply big_sepM_from_Forall; eauto.
Qed.

Instance big_sepM_FromPure {PROP: bi} `{Countable K} {V}
          `{BiAffine PROP}
          (Φ: K → V → PROP) (P: K → V → Prop)
          {ΦP: ∀ k v, FromPure false (Φ k v) (P k v)}
          (m: gmap K V) :
  FromPure false ([∗ map] k↦x ∈ m, Φ k x) (map_Forall P m).
Proof.
  hnf; simpl.
  iIntros "%".
  iApply big_sepM_from_Forall; eauto.
Qed.

Lemma big_sepM_lookup_holds {PROP:bi} `{Countable K} {V}
      `{BiAffine PROP} (m: gmap K V) :
  ⊢@{PROP} [∗ map] k↦v ∈ m, ⌜m !! k = Some v⌝.
Proof.
  iPureIntro.
  apply map_Forall_lookup; auto.
Qed.

Section big_sepms_def.

  Context {PROP : bi}.
  Context `{Countable K}.

  Inductive bsm_maps : Type :=
  | bsm_cons : ∀ {T : Type} (m : gmap K T) (ms' : bsm_maps), bsm_maps
  | bsm_nil : bsm_maps
  .

  Fixpoint bsm_pred (ms : bsm_maps) : Type :=
    match ms with
    | @bsm_cons T _ ms' => T -> bsm_pred ms'
    | bsm_nil => PROP
    end.

  Fixpoint bsm_keys_match (keys : gset K) (ms : bsm_maps) : Prop :=
    match ms with
    | @bsm_cons T m ms' =>
      keys = dom (gset K) m ∧
      bsm_keys_match keys ms'
    | bsm_nil => True
    end.

  Fixpoint bsm_key_pred (k : K) (ms : bsm_maps) (P : bsm_pred ms) {struct ms} : PROP.
    destruct ms.
    - exact (∃ (v : T), ⌜ m !! k = Some v ⌝ ∗ bsm_key_pred k ms (P v))%I.
    - exact P.
  Defined.

  Definition big_sepMs (ms : bsm_maps) (P : K -> bsm_pred ms) : PROP :=
    ( ∃ (keys : gset K),
        ⌜ bsm_keys_match keys ms ⌝ ∗
        [∗ set] k ∈ keys, bsm_key_pred k ms (P k)
    )%I.

End big_sepms_def.

Declare Scope big_sepms_maps_scope.
Delimit Scope big_sepms_maps_scope with big_sepms_maps.
Notation "[ mx ]" :=
  (bsm_cons mx bsm_nil)
  : big_sepms_maps_scope.
Notation "[ mx ; my ; .. ; mz ]" :=
  (bsm_cons mx (bsm_cons my .. (bsm_cons mz bsm_nil) ..))
  : big_sepms_maps_scope.

Notation "'[∗' 'maps]' k ↦ x ; .. ; y ∈ ms , P" :=
  (big_sepMs ms%big_sepms_maps (fun k => (fun x => .. (fun y => P) .. )))
  (at level 200, ms at level 10, k at level 1,
   x closed binder, y closed binder,
   right associativity,
   format "[∗  maps]  k ↦ x ; .. ; y  ∈  ms ,  P")
  : bi_scope.

Section big_sepms.

  Context {PROP : bi}.
  Context `{Countable K}.
  Variable (A : Type).

  Theorem big_sepM_sepMs (m : gmap K A) (P : K -> A -> PROP):
    ( [∗ map] k ↦ v ∈ m, P k v ) -∗
    [∗ maps] k ↦ v ∈ [m], P k v.
  Proof.
  Abort.

End big_sepms.
