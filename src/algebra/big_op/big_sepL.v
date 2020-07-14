From iris.algebra Require Export big_op.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

Set Default Proof Using "Type".

Section list.
  Context {PROP : bi}.
  Implicit Types (P Q : PROP).
  Implicit Types (A : Type).

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
    length l1 = length l2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ (n+k) y1 y2) ⊣⊢
    ([∗ list] k↦y1 ∈ l1, ∃ y2, ⌜l2 !! k = Some y2⌝ ∧ Φ (n+k) y1 y2).
  Proof.
    intros Hlen.
    (iInduction l1 as [|y1 l1] "IH" forall (n l2 Hlen)).
    - assert (l2 = []); subst; simpl.
      { apply length_zero_iff_nil; auto. }
      auto.
    - destruct l2 as [|y2 l2].
      { simpl in Hlen; congruence. }
      inversion Hlen; subst; clear Hlen.
      iSpecialize ("IH" $! (S n) l2 with "[% //]").
      rewrite big_sepL2_cons big_sepL_cons /=.
      assert (forall k, n + S k = S (n + k)) as Harith by lia.
      setoid_rewrite Harith.
      iSplit.
      + iIntros "[HΦ Hl]".
        iSplitL "HΦ"; first by eauto with iFrame.
        iApply ("IH" with "Hl").
      + iIntros "[HΦ Hl]".
        iDestruct "HΦ" as (y) "[%Heq HΦ]".
        inversion Heq; subst; iFrame.
        iApply ("IH" with "Hl").
  Qed.

  Lemma big_sepL2_to_sepL_1 Φ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) -∗
    ([∗ list] k↦y1 ∈ l1, ∃ y2, ⌜l2 !! k = Some y2⌝ ∧ Φ k y1 y2).
  Proof.
    iIntros "H".
    iDestruct (big_sepL2_length with "H") as %Hlen.
    iApply (big_sepL2_to_sepL_aux Φ 0 with "H"); auto.
  Qed.

  Lemma big_sepL2_to_sepL_2 (Φ: nat → B → A → PROP) l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) -∗
    ([∗ list] k↦y2 ∈ l2, ∃ y1, ⌜l1 !! k = Some y1⌝ ∧ Φ k y1 y2).
  Proof. rewrite big_sepL2_flip big_sepL2_to_sepL_1 //. Qed.

  (* expressed as an equivalence, but needs a separate length assumption (to
  strengthen the right-hand side) *)
  Lemma big_sepL2_to_sepL_1' Φ l1 l2 :
    length l1 = length l2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
    ([∗ list] k↦y1 ∈ l1, ∃ y2, ⌜l2 !! k = Some y2⌝ ∧ Φ k y1 y2).
  Proof.
    apply (big_sepL2_to_sepL_aux Φ 0).
  Qed.

  Lemma big_sepL2_to_sepL_2' (Φ: nat → B → A → PROP) l1 l2 :
    length l1 = length l2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
    ([∗ list] k↦y2 ∈ l2, ∃ y1, ⌜l1 !! k = Some y1⌝ ∧ Φ k y1 y2).
  Proof. intros. rewrite big_sepL2_flip big_sepL2_to_sepL_1' //. Qed.

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
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) -∗
    ⌜l1 !! i = None⌝.
  Proof.
    iIntros (?) "H".
    apply lookup_ge_None in H as Hlen.
    iDestruct (big_sepL2_length with "H") as %Hslen.
    rewrite -Hslen in Hlen.
    apply lookup_ge_None in Hlen.
    eauto.
  Qed.
End list2.

End list.
