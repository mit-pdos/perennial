From iris.algebra Require Export big_op.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type*".
Local Existing Instances monoid_ne monoid_assoc monoid_comm
  monoid_left_id monoid_right_id monoid_proper
  monoid_homomorphism_rel_po monoid_homomorphism_rel_proper
  monoid_homomorphism_op_proper
  monoid_homomorphism_ne weak_monoid_homomorphism_proper.

From iris.bi Require Import derived_laws_sbi plainly big_op.
Import interface.bi derived_laws_bi.bi derived_laws_sbi.bi.

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
End map.

Section list.

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

Section maplist.
  Context `{Countable K} {V LV : Type}.
  Implicit Types Φ Ψ : K → V → LV → PROP.
  Implicit Types m : gmap K V.
  Implicit Types l : list LV.

  Definition big_sepML Φ m l : PROP :=
    (∃ lm,
      ⌜ l ≡ₚ map snd (map_to_list lm) ⌝ ∗
      [∗ map] k ↦ v;lvm ∈ m;lm, Φ k v lvm)%I.

  Global Instance big_sepML_proper :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊢)))
       ==> (=) ==> (Permutation) ==> (⊢))
           (big_sepML).
  Proof.
    intros P0 P1 HP.
    intros m0 m Hm; subst.
    intros l0 l1 Hl.
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
    rewrite /big_sepML.
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

  Theorem big_sepML_delete_m Φ m l k v `{!∀ k v lv, Absorbing (Φ k v lv)} :
    m !! k = Some v ->
    big_sepML Φ m l -∗
    ∃ i lv,
      ⌜ l !! i = Some lv ⌝ ∗
      Φ k v lv ∗
      big_sepML Φ (delete k m) (delete i l).
  Proof.
    iIntros (Hm) "Hml".
  Admitted.

  Theorem big_sepML_lookup_l_acc Φ m l i lv `{!∀ k v lv, Absorbing (Φ k v lv)} :
    l !! i = Some lv ->
    big_sepML Φ m l -∗
    ∃ k v, ⌜ m !! k = Some v ⌝ ∗ Φ k v lv ∗
    ∀ v' lv',
      Φ k v' lv' -∗
      big_sepML Φ (<[k := v']> m) (<[i := lv']> l).
  Proof.
  Admitted.

  Theorem big_sepML_lookup_l_app_acc Φ m lv l0 l1 `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ m (l0 ++ lv :: l1) -∗
    ∃ k v, ⌜ m !! k = Some v ⌝ ∗ Φ k v lv ∗
    ∀ v' lv',
      Φ k v' lv' -∗
      big_sepML Φ (<[k := v']> m) (l0 ++ lv' :: l1).
  Proof.
  Admitted.

  Theorem big_sepML_lookup_m_acc Φ m l k v `{!∀ k v lv, Absorbing (Φ k v lv)} :
    m !! k = Some v ->
    big_sepML Φ m l -∗
    ∃ i lv, ⌜ l !! i = Some lv ⌝ ∗ Φ k v lv ∗
    ∀ v' lv',
      Φ k v' lv' -∗
      big_sepML Φ (<[k := v']> m) (<[i := lv']> l).
  Proof.
  Admitted.

  Theorem big_sepML_mono Φ Ψ m l `{!∀ k v lv, Absorbing (Φ k v lv)} `{!∀ k v lv, Absorbing (Ψ k v lv)} :
    big_sepML Φ m l -∗
    ⌜ ∀ k v lv, Φ k v lv -∗ Ψ k v lv ⌝ -∗
    big_sepML Ψ m l.
  Proof.
    rewrite /big_sepML; iIntros "Hml %".
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
  Admitted.

  Theorem big_sepML_empty_l Φ l `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ ∅ l -∗
    ⌜ l = [] ⌝.
  Proof.
  Admitted.

  Theorem big_sepML_fmap_m Φ m l f `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ (f <$> m) l -∗
    big_sepML (λ k v lv, Φ k (f v) lv) m l.
  Proof.
  Admitted.

  Theorem big_sepML_fmap_m' Φ m l f `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML (λ k v lv, Φ k (f v) lv) m l -∗
    big_sepML Φ (f <$> m) l.
  Proof.
  Admitted.

End maplist.

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
