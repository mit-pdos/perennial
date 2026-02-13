From New.generatedproof Require Import slices.
From New.proof Require Import proof_prelude.
From New.proof.slices_proof Require Import slices_init.
From New.proof.slices_proof.pdqSort Require Import sort_basics.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : slices.Assumptions}.

Context `[!ZeroVal E] `[!TypedPointsto E] `[!IntoValTyped E Et].
Context (R: E → E → Prop) `{!StrictWeakOrder R} `{!RelDecision R}.
Collection W := sem + package_sem + IntoValTyped0.

#[local] Infix "≺" := R (at level 70).
#[local] Notation "x ≽ y" := (¬ R x y) (at level 70, only parsing).

Lemma wp_insertionSortCmpFunc (data: slice.t) (a b: w64) (cmp : func.t)
                       (xs: list E):
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦* xs ∗
      "#Hcmp" ∷ cmp_implements R cmp ∗
      "%Hab_bound" ∷ ⌜ 0 ≤ sint.Z a ≤ sint.Z b ≤ length xs ∧ length xs <= 2 ^ 62⌝
  }}}
    #(functions slices.insertionSortCmpFunc [Et]) #data #a #b #cmp
  {{{ (xs': list E), RET #();
      data ↦* xs' ∗
      "%Hperm" ∷ ⌜ Permutation xs xs' ⌝ ∗
      "%Hsorted" ∷ ⌜ is_sorted_seg R xs' (sint.nat a) (sint.nat b) ⌝ ∗
      "%Houtside" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
  }}}.

Proof using StrictWeakOrder0 + RelDecision0 + W.
  wp_start as "H". iNamed "H". wp_auto.
  iDestruct (own_slice_len with "[$]") as "%Hlen".
  destruct (Nat.eq_dec (sint.nat a) (sint.nat b)) as [Heq4 | Hneq4].
  {
    (* Trivial Case: a = b, no change to the list *)
    iAssert(
      "a" ∷ a_ptr ↦ a ∗
      "b" ∷ b_ptr ↦ b ∗
      "cmp" ∷ cmp_ptr ↦ cmp ∗
      "i" ∷ (i_ptr ↦ word.add a (W64 1)) ∗
      "Hxs1" ∷ data ↦* xs
    )%I with "[a b cmp Hxs i]" as "HI".
    { iFrame. }
    wp_for "HI". wp_if_destruct.
    - word.
    - iApply "HΦ". iFrame. iSplit; auto. iPureIntro.
      split; try apply outside_same_refl.
      unfold is_sorted_seg. intros. lia.
  }
  iPersist "a b".
  (* Loop Invariant for the outer loop *)
  iAssert( ∃ (i_val: w64) xs',
    "cmp" ∷ cmp_ptr ↦ cmp ∗
    "i" ∷ i_ptr ↦ i_val ∗
    "Hxs1" ∷ data ↦* xs' ∗
    "%irange" ∷ ⌜ sint.Z a + 1 ≤ sint.Z i_val ≤ sint.Z b ⌝ ∗
    "%HPerm1" ∷ ⌜ Permutation xs xs' ⌝ ∗
    "%Hsorted" ∷ ⌜ is_sorted_seg R xs' (sint.nat a) (sint.nat i_val) ⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
  )%I with "[cmp Hxs i]" as "HI1".
  { iFrame. iSplit. -word. -iPureIntro. split; auto. unfold is_sorted_seg. split; intros; try word.
    unfold outside_same; intros. auto. }
  wp_for "HI1". wp_if_destruct.
  - (* Loop Invariant for the inner loop *)
    iAssert( ∃ (j_val: w64) xs'',
      "cmp" ∷ cmp_ptr ↦ cmp ∗
      "i" ∷ i_ptr ↦ i_val ∗
      "j" ∷ j_ptr ↦ j_val ∗
      "%jrange" ∷ ⌜ sint.Z a ≤ sint.Z j_val ≤ sint.Z i_val ⌝ ∗
      "Hxs2" ∷ data ↦* xs'' ∗
      "%Hperm2" ∷ ⌜ Permutation xs xs'' ⌝ ∗
      "%HsortedBr" ∷ ⌜ ∀ i j xi xj, (sint.nat a <= i < j)%nat ∧ j ≤ sint.nat i_val -> j ≠ sint.nat j_val -> xs'' !! i = Some xi -> xs'' !! j = Some xj -> xj ≽ xi ⌝  ∗
      "%Houtside2" ∷ ⌜ outside_same xs xs'' (sint.nat a) (sint.nat b) ⌝
    )%I with "[cmp i j Hxs1]" as "HI2".
    { iFrame. iSplit; iPureIntro. -lia. -split; auto.
      unfold is_sorted_seg in Hsorted. split; eauto.
      intros. eapply Hsorted; eauto. lia. }
    wp_for "HI2". wp_if_destruct.
    + assert(length xs = length xs''). { apply Permutation_length. auto. }
      rewrite H in Hlen Hab_bound. clear H.
      assert(∃ x : E, xs'' !! sint.nat j_val = Some x). { apply list_lookup_lt. lia. }
      destruct H as [x0 H0].
      assert(∃ x : E, xs'' !! (sint.nat ((word.sub) j_val (W64 1)))%nat = Some x). { apply list_lookup_lt. word. }
      destruct H as [x1 H1].

      (* read data[j] *)
      rewrite -> decide_True; last lia.
      wp_apply (wp_load_slice_index with "[$Hxs2]") as "Hxs2"; eauto; try lia.
      (* read data[j-1] *)
      rewrite -> decide_True; last word.
      wp_apply (wp_load_slice_index with "[$Hxs2]") as "Hxs2"; eauto; try word.

      wp_apply "Hcmp". iIntros (r) "%Hcmp_r". wp_auto.
      wp_if_destruct.
      * (* read old data[j-1] *)
        rewrite -> decide_True; last word.
        wp_apply (wp_load_slice_index with "[$Hxs2]") as "Hxs2"; eauto; try word.

        (* read old data[j] *)
        rewrite -> decide_True; last word.
        wp_apply (wp_load_slice_index with "[$Hxs2]") as "Hxs2"; eauto; try lia.

        (* write new data[j] *)
        rewrite -> decide_True; last word. wp_auto.
        wp_apply (wp_store_slice_index with "[$Hxs2]") as "Hxs2"; first word.

        (* write new data[j-1] *)
        rewrite -> decide_True; last word. wp_auto.
        wp_apply (wp_store_slice_index with "[$Hxs2]") as "Hxs2". { rewrite length_insert. word. }

        wp_for_post. iFrame.
        assert((sint.nat (word.sub j_val (W64 1))) = (sint.nat j_val - 1)%nat) by word.
        replace (sint.nat (word.sub j_val (W64 1))) with (sint.nat j_val - 1)%nat in *; auto.
        clear H.
        iSplit; try word. {
          iPureIntro. split; try split. (* The pure fact, mainly about ordering *)
          - eapply perm_trans with xs''; auto. apply swap_perm; eauto.
          - intros. apply Hcmp_r in l0. clear Hcmp_r.
            destruct (Nat.eq_dec j (sint.nat j_val)) as [Heq | Hneq].
            + rewrite list_lookup_insert_ne in H4; try lia.
              subst j. rewrite list_lookup_insert_eq in H4; try lia. inv H4.
              destruct (Nat.eq_dec i (sint.nat j_val - 1)%nat) as [Heq2 | Hneq2].
              * subst i.
                assert(length (<[sint.nat j_val:=xj]> xs'') = length xs''). { apply length_insert. }
                rewrite list_lookup_insert_eq in H3; try lia. inv H3.
                assert(¬ xj ≺ xi ∨ ¬ xi ≺ xj). { apply notR_comparable; auto. }
                destruct H3; auto.
              * apply (HsortedBr i (sint.nat j_val - 1)%nat); auto; try lia.
                assert(length (<[sint.nat j_val:=x0]> xs'') = length xs''). { apply length_insert. }
                rewrite list_lookup_insert_ne in H3; try lia.
                rewrite list_lookup_insert_ne in H3; try lia. auto.
            + rewrite list_lookup_insert_ne in H4; auto. rewrite list_lookup_insert_ne in H4; auto.
              destruct (Nat.eq_dec i (sint.nat j_val - 1)%nat) as [Heq2 | Hneq2].
              * subst i. assert(length (<[sint.nat j_val:=x1]> xs'') = length xs''). { apply length_insert. }
                rewrite list_lookup_insert_eq in H3; try lia. inv H4.
                eapply (HsortedBr (sint.nat j_val)%nat j); eauto; try lia.
              * rewrite list_lookup_insert_ne in H3; auto. destruct (Nat.eq_dec i (sint.nat j_val)%nat) as [Heq3 | Hneq3].
                ** rewrite <- Heq3 in H3. rewrite list_lookup_insert_eq in H3; auto; try lia. inv H4.
                   eapply (HsortedBr (sint.nat j_val - 1)%nat j); eauto. lia.
                ** rewrite list_lookup_insert_ne in H3; auto. eapply HsortedBr; eauto.
          - eapply outside_same_trans; eauto. eapply outside_same_swap; lia.
        }
      * wp_for_post. (* Exiting inner loop because already sorted *)
        iFrame. iSplit; try word. { iPureIntro. split; try split; auto.
          unfold is_sorted_seg. intros. destruct (Nat.eq_dec j (sint.nat j_val)) as [Heq | Hneq].
          + replace (sint.nat ((word.sub) j_val (W64 1))) with (j - 1)%nat in H1 by word.
            apply comparison_negate in Hcmp_r. apply Hcmp_r in n. subst j. rewrite H0 in H3. inv H3.
            eapply notR_trans; eauto. destruct (Nat.eq_dec i (sint.nat j_val -1)%nat) as [Heq1 | Hneq1].
            * rewrite Heq1 in H2. rewrite H2 in H1. inv H1. apply notR_refl; auto.
            * eapply (HsortedBr i (sint.nat j_val - 1)%nat); eauto; lia.
          + eapply HsortedBr; eauto. word.
        }

    + wp_for_post. (* Exiting inner loop with j = a *)
      iFrame. iSplit. { word. } { iPureIntro. split; try split; auto.
        unfold is_sorted_seg. intros. apply (HsortedBr i j); eauto; try lia. word.
      }
  - iApply "HΦ". iFrame. iPureIntro. split; try split; auto.
    unfold is_sorted_seg in *. intros. apply (Hsorted i j); eauto. lia.
Qed.


Lemma wp_partialInsertionSortCmpFunc (data: slice.t) (a b: w64) (cmp_code: func.t)
                       (xs: list E):
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦* xs ∗
      "#Hcmp" ∷ cmp_implements R cmp_code ∗
      "%Header" ∷ ⌜ header R xs (sint.nat a) (sint.nat b) ⌝ ∗
      "%Hab_bound" ∷ ⌜ 0 ≤ sint.Z a < sint.Z b ∧ sint.Z b ≤ length xs ∧ length xs <= 2 ^ 62⌝
  }}}
    @! slices.partialInsertionSortCmpFunc #Et #data #a #b #cmp_code
  {{{ (xs': list E) (bl: bool), RET #bl;
      data ↦* xs' ∗
      "%Hperm" ∷ ⌜ Permutation xs xs' ⌝ ∗
      "%Hsorted" ∷ ⌜ if bl then is_sorted_seg R xs' (sint.nat a) (sint.nat b) else True ⌝ ∗
      "%Houtside" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
  }}}.
Proof using StrictWeakOrder0 RelDecision0.
  wp_start as "H". iNamed "H". wp_auto.
  iAssert(⌜length xs = sint.nat data .(slice.len_f) ∧ 0 ≤ sint.Z data .(slice.len_f)⌝)%I
  with "[Hxs]" as "%Hlen". { iApply own_slice_len. iFrame. }
  iAssert ( ∃ (i_val j_val: w64) xs',
    "a" ∷ a_ptr ↦ a ∗
    "b" ∷ b_ptr ↦ b ∗
    "cmp" ∷ cmp_ptr ↦ cmp_code ∗
    "data" ∷ data_ptr ↦ data ∗
    "i" ∷ i_ptr ↦ i_val ∗
    "j" ∷ j_ptr ↦ j_val ∗
    "Hxs1" ∷ data ↦* xs' ∗
    "%irange" ∷ ⌜ sint.Z a + 1 ≤ sint.Z i_val ≤ sint.Z b ⌝ ∗
    "%HPerm1" ∷ ⌜ Permutation xs xs' ⌝ ∗
    "%Hsorted" ∷ ⌜ is_sorted_seg R xs' (sint.nat a) (sint.nat i_val) ⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
  )%I with "[a b cmp Hxs i j data]" as "HI1".
  { iFrame. iPureIntro; split_and!; auto; try word.
    - unfold is_sorted_seg. intros. word.
    - apply outside_same_refl. }

  wp_for "HI1". wp_if_destruct. {
      set HI := ( ∃ (i_val: w64) xs',
        "a" ∷ a_ptr ↦ a ∗
        "b" ∷ b_ptr ↦ b ∗
        "cmp" ∷ cmp_ptr ↦ cmp_code ∗
        "data" ∷ data_ptr ↦ data ∗
        "i" ∷ i_ptr ↦ i_val ∗
        "j" ∷ j_ptr ↦ j_val ∗
        "Hxs1" ∷ data ↦* xs' ∗
        "%irange" ∷ ⌜ sint.Z a + 1 ≤ sint.Z i_val ≤ sint.Z b ⌝ ∗
        "%HPerm1" ∷ ⌜ Permutation xs xs' ⌝ ∗
        "%Hsorted" ∷ ⌜ is_sorted_seg R xs' (sint.nat a) (sint.nat i_val) ⌝ ∗
        "%Houtside1" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
      )%I.
      wp_bind. iApply ((wp_wand _ _ _ (fun v => ⌜ v = execute_val ⌝ ∗ ( ∃ (i_val: w64) xs',
        "a" ∷ a_ptr ↦ a ∗
        "b" ∷ b_ptr ↦ b ∗
        "cmp" ∷ cmp_ptr ↦ cmp_code ∗
        "i" ∷ i_ptr ↦ i_val ∗
        "data" ∷ data_ptr ↦ data ∗
        "j" ∷ j_ptr ↦ j_val ∗
        "Hxs1" ∷ data ↦* xs' ∗
        "%irange" ∷ ⌜ sint.Z a + 1 ≤ sint.Z i_val ≤ sint.Z b ⌝ ∗
        "%HPerm1" ∷ ⌜ Permutation xs xs' ⌝ ∗
        "%Hsorted" ∷ ⌜ is_sorted_seg R xs' (sint.nat a) (sint.nat i_val) ⌝ ∗
        "%Houtside1" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝ ∗
        "%HBr" ∷ ⌜ sint.nat i_val = sint.nat b \/ forall x0 x1, xs' !! (sint.nat i_val - 1)%nat = Some x0 -> xs' !! (sint.nat i_val) = Some x1 -> x0 ≽ x1 ⌝
      ))%I) with "[a b Hxs1 i j data cmp]"). {
      iAssert HI with "[a b cmp Hxs1 i j data]" as "HI2".
      { unfold HI. iFrame. iPureIntro. split; first word. auto. }
      wp_for "HI2". wp_if_destruct. {
        clear dependent i_val xs'.
        rename i_val0 into i_val. rename xs'0 into xs'.
        assert(length xs = length xs'). { apply Permutation_length; auto. }
        iAssert(⌜length xs' = sint.nat data .(slice.len_f) ∧ 0 ≤ sint.Z data .(slice.len_f)⌝)%I
        with "[Hxs1]" as "%Hlen2". { iApply own_slice_len. iFrame. }
        wp_pure; first lia.
        assert(∃ x : E, xs' !! sint.nat i_val = Some x). { apply list_lookup_lt. lia. } destruct H0 as [x1 Hx1].
        wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs"; eauto; try lia.

        wp_pure; first word.
        assert(sint.nat (word.sub i_val (W64 1)) = (sint.nat i_val - 1)%nat) by word.
        assert(∃ x : E, xs' !! sint.nat (word.sub i_val (W64 1)) = Some x). { apply list_lookup_lt. lia. } destruct H1 as [x0 Hx0].
        wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try word.
        wp_apply "Hcmp". iIntros (r) "%Hcmp_r". wp_auto. wp_if_destruct.
        - iSplit; auto. iFrame. iPureIntro. split_and!; auto; try lia.
          right. intros. apply Hcmp_r in l1.
          rewrite H0 in Hx0. rewrite Hx1 in H2. rewrite H1 in Hx0. inv H2.
          apply R_antisym; auto.
        - wp_for_post. unfold HI. iFrame. iPureIntro. split_and!; auto; try word. unfold is_sorted_seg.
          replace (sint.nat (word.add i_val (W64 1))) with (sint.nat i_val + 1)%nat by word.
          intros. unfold is_sorted_seg in *.
          destruct (Nat.eq_dec j (sint.nat i_val)) as [Heq2 | Hneq2].
          + subst j. apply comparison_negate in Hcmp_r. apply Hcmp_r in n.
            rewrite H3 in Hx1. inv Hx1. eapply notR_trans; try apply n; auto.
            destruct (Nat.eq_dec i (sint.nat i_val - 1)%nat) as [Heq2 | Hneq2].
            * rewrite H0 in Hx0. subst i. rewrite H2 in Hx0. inv Hx0.
            apply notR_refl; auto.
            * eapply Hsorted0; eauto; lia.
          + eapply Hsorted0; eauto; lia.
      }
      {
        iSplit; auto. iFrame. iPureIntro. split_and!; auto; try lia.
      }
    }
    iIntros (v) "[%Hv HI]". subst v. iNamed "HI". wp_auto.
    wp_if_destruct. {
      wp_for_post. iApply "HΦ"; iFrame; auto.
    }
    assert(sint.Z i_val0 ≠ sint.Z b) by word.
    assert(sint.nat i_val0 ≠ sint.nat b) by word.
    wp_if_destruct. {
      wp_for_post. iApply "HΦ"; iFrame; auto.
    }
    clear dependent i_val xs'. rename i_val0 into i_val. rename xs'0 into xs'.
    assert(length xs = length xs'). { apply Permutation_length; auto. }
    iAssert(⌜length xs' = sint.nat data .(slice.len_f) ∧ 0 ≤ sint.Z data .(slice.len_f)⌝)%I
    with "[Hxs1]" as "%Hlen2". { iApply own_slice_len. iFrame. }

    assert(sint.Z (word.sub i_val (W64 1)) = sint.Z i_val - 1) by word.
    assert(sint.nat (word.sub i_val (W64 1)) = (sint.nat i_val - 1)%nat) by word.

    wp_pure; first lia.
    assert(∃ x : E, xs' !! sint.nat i_val = Some x). { apply list_lookup_lt. lia. } destruct H4 as [x1 Hx1].
    assert(∃ x : E, xs' !! sint.nat (word.sub i_val (W64 1)) = Some x). { apply list_lookup_lt. lia. } destruct H4 as [x0 Hx0].
    wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs"; eauto; try lia.

    wp_pure; first lia.
    wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

    (* write new data[j] *)
    wp_pure; first lia.
    wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; first word.

    (* write new data[j-1] *)
    wp_pure; first word.
    wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs". { rewrite length_insert. word. }
    rename j_ptr into j_ptr0; rename j_val into j_val0; iRename "j" into "j0".

    wp_bind. iApply ((wp_wand _ _ _ (fun v => ⌜ v = execute_val ⌝ ∗ HI)%I) with "[a b Hxs i j0 data cmp]"). {
      wp_if_destruct. {
        iAssert( ∃ (j_val: w64) xs',
          "a" ∷ a_ptr ↦ a ∗
          "b" ∷ b_ptr ↦ b ∗
          "cmp" ∷ cmp_ptr ↦ cmp_code ∗
          "i" ∷ i_ptr ↦ i_val ∗
          "j" ∷ j_ptr ↦ j_val ∗
          "j0" ∷ j_ptr0 ↦ j_val0 ∗
          "%jrange" ∷ ⌜ sint.Z a ≤ sint.Z j_val ≤ sint.Z i_val ⌝ ∗
          "Hxs2" ∷ data ↦* xs' ∗
          "%Hperm2" ∷ ⌜ Permutation xs xs' ⌝ ∗
          "%HsortedBr" ∷ ⌜ ∀ i j xi xj, (sint.nat a <= i < j)%nat ∧ j < sint.nat i_val -> j ≠ sint.nat j_val -> xs' !! i = Some xi -> xs' !! j = Some xj -> xj ≽ xi ⌝  ∗
          "%Houtside2" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
        )%I with "[a b cmp i j j0 Hxs]" as "HI2".
        { iFrame. iPureIntro; split_and!; try lia.
          - eapply perm_trans; eauto. eapply swap_perm; eauto.
          - intros. rewrite list_lookup_insert_ne in H7; try lia.
            rewrite list_lookup_insert_ne in H6; try lia.
            rewrite list_lookup_insert_ne in H7; try lia.
            rewrite list_lookup_insert_ne in H6; try lia.
            unfold is_sorted_seg in Hsorted0.
            eapply Hsorted0; eauto. lia.
          - eapply outside_same_trans; eauto. eapply outside_same_swap; lia.
        }
        clear dependent xs'. wp_for "HI2".
        wp_if_destruct. {
          clear dependent x0 x1.
          assert(length xs = length xs'). { apply Permutation_length; auto. }
          iAssert(⌜length xs' = sint.nat data .(slice.len_f) ∧ 0 ≤ sint.Z data .(slice.len_f)⌝)%I
          with "[Hxs2]" as "%Hlen2". { iApply own_slice_len. iFrame. }

          assert(sint.Z j_val > 0) by word.
          assert(sint.nat j_val > 0)%nat by word.
          assert(sint.Z (word.sub j_val (W64 1)) = sint.Z j_val - 1) by word.
          assert(sint.nat (word.sub j_val (W64 1)) = (sint.nat j_val - 1)%nat) by word.

          assert(∃ x : E, xs' !! sint.nat j_val = Some x). { apply list_lookup_lt. lia. } destruct H8 as [x1 Hx1].
          assert(∃ x : E, xs' !! sint.nat (word.sub j_val (W64 1)) = Some x). { apply list_lookup_lt. lia. } destruct H8 as [x0 Hx0].

          wp_pure; first lia.
          wp_apply (wp_load_slice_index with "[$Hxs2]") as "Hxs"; eauto; try lia.

          wp_pure; first lia.
          wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

          wp_apply "Hcmp". iIntros (r) "%Hcmp_r". wp_auto. wp_if_destruct. {
            wp_pure; first lia.
            wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

            wp_pure; first lia.
            wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.
            wp_pure; first lia.
            wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; first (iPureIntro; word).

            (* write new data[j-1] *)
            wp_pure; first word.
            wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs". { rewrite length_insert. iPureIntro. lia. }

            wp_for_post. iFrame. iPureIntro. apply Hcmp_r in l0.
            assert(sint.Z a < sint.Z j_val). {
              destruct (Z.eq_dec (sint.Z a) (sint.Z j_val)) as [Heq | Hneq].
              {
                symmetry in Heq. inv Heq.
                assert(header R xs' (sint.nat a) (sint.nat b)). {
                  eapply header__preserve; eauto. lia.
                }
                unfold header in H8. unfold one_le_seg in H8.
                destruct (decide (sint.nat a = 0%nat)) as [Ha|Ha].
                - lia.
                - specialize H8 with x0 (sint.nat a) x1.
                  rewrite H7 in Hx0. destruct H8; auto. lia.
              } {
                lia.
              }
            }
            split_and!; try lia.
            - eapply perm_trans; eauto. apply swap_perm; eauto.
            - intros. rewrite H7 in H10 H11 H12 Hx0.
              rewrite list_lookup_insert_ne in H12; auto.
              destruct (Nat.eq_dec j (sint.nat j_val)) as [Heqj|Hneqj].
              + subst j. rewrite list_lookup_insert_eq in H12; try lia. inv H12.
                destruct (Nat.eq_dec i (sint.nat j_val - 1)%nat) as [Heqi | Hneqi].
                * subst i. rewrite list_lookup_insert_eq in H11; try (rewrite length_insert;lia).
                  inv H11. apply R_antisym; auto.
                * rewrite list_lookup_insert_ne in H11; try lia.
                  rewrite list_lookup_insert_ne in H11; try lia.
                  eapply (HsortedBr i (sint.nat j_val - 1)%nat); eauto. lia.
              + rewrite list_lookup_insert_ne in H12; auto.
                destruct (Nat.eq_dec i (sint.nat j_val - 1)%nat) as [Heqi1|Hneqi1].
                * subst i. rewrite list_lookup_insert_eq in H11; try (rewrite length_insert;lia). inv H11.
                  eapply (HsortedBr (sint.nat j_val)%nat); eauto. lia.
                * rewrite list_lookup_insert_ne in H11; auto.
                  destruct (Nat.eq_dec i (sint.nat j_val)) as [Heqi2|Hneqi2].
                  -- subst i. rewrite list_lookup_insert_eq in H11; try lia.
                     inv H11. eapply (HsortedBr (sint.nat j_val - 1)%nat); eauto. lia.
                  -- rewrite list_lookup_insert_ne in H11; auto.
                     eapply (HsortedBr); eauto.
            - eapply outside_same_trans; eauto. eapply outside_same_swap; lia.
          } {
            wp_for_post. iSplit; auto. unfold HI. iFrame. iPureIntro.
            split_and!; auto; try lia.
            unfold is_sorted_seg in *. intros.
            destruct (Nat.eq_dec j (sint.nat j_val)) as [Heq2 | Hneq2].
            - subst j. apply comparison_negate in Hcmp_r. apply Hcmp_r in n1.
              rewrite H7 in Hx0. inv Hx1. eapply notR_trans; eauto.
              destruct (Nat.eq_dec i (sint.nat j_val - 1)%nat) as [Heq2 | Hneq2].
              + subst i. rewrite Hx0 in H9. inv H9. apply notR_refl. auto.
              + eapply HsortedBr; try eapply Hx0; try eapply Hx0; eauto; lia.
            - eapply HsortedBr; eauto; lia.
          }
        } {
          iSplit; auto. unfold HI. iFrame.
          iPureIntro; split_and!; try lia; auto.
          unfold is_sorted_seg. intros.
          eapply HsortedBr; try eapply H4; try eapply H5; word.
        }
      } {
        iSplit; auto. unfold HI. iFrame.
        iPureIntro; split_and!; auto; try lia.
        - eapply perm_trans; eauto. eapply swap_perm; eauto.
        - unfold is_sorted_seg. intros. word.
        - eapply outside_same_trans; eauto. eapply outside_same_swap; lia.
      }
    }
    iIntros (v) "[%Hv HI]". subst v. iNamed "HI". wp_auto.
    wp_bind. iApply ((wp_wand _ _ _ (fun v => ⌜ v = execute_val ⌝ ∗ HI)%I) with "[a b Hxs1 i j data cmp]"). {
      wp_if_destruct. {
        iRename "j" into "j0". wp_auto.
        clear dependent xs' i_val. rename xs'0 into xs'. rename i_val0 into i_val.
        iAssert( ∃ (j_val: w64) xs',
          "a" ∷ a_ptr ↦ a ∗
          "b" ∷ b_ptr ↦ b ∗
          "cmp" ∷ cmp_ptr ↦ cmp_code ∗
          "i" ∷ i_ptr ↦ i_val ∗
          "j" ∷ j_ptr ↦ j_val ∗
          "j0" ∷ j_ptr0 ↦ j_val0 ∗
          "%jrange" ∷ ⌜ sint.Z i_val < sint.Z j_val ≤ sint.Z b ⌝ ∗
          "Hxs2" ∷ data ↦* xs' ∗
          "%Hperm2" ∷ ⌜ Permutation xs xs' ⌝ ∗
          "%Hsorted" ∷ ⌜ is_sorted_seg R xs' (sint.nat a) (sint.nat i_val) ⌝  ∗
          "%Houtside2" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
        )%I with "[a b cmp i j j0 Hxs1]" as "HI2".
        { iFrame. iSplit; first word. auto. }
        wp_for "HI2". wp_if_destruct. {
          clear dependent xs' x0 x1. rename xs'0 into xs'.
          assert(length xs = length xs'). { apply Permutation_length; auto. }
          iAssert(⌜length xs' = sint.nat data .(slice.len_f) ∧ 0 ≤ sint.Z data .(slice.len_f)⌝)%I
          with "[Hxs2]" as "%Hlen2". { iApply own_slice_len. iFrame. }

          assert(sint.Z (word.sub j_val (W64 1)) = sint.Z j_val - 1) by word.
          assert(sint.nat (word.sub j_val (W64 1)) = (sint.nat j_val - 1)%nat) by word.

          assert(∃ x : E, xs' !! sint.nat j_val = Some x). { apply list_lookup_lt. lia. } destruct H2 as [x1 Hx1].
          assert(∃ x : E, xs' !! sint.nat (word.sub j_val (W64 1)) = Some x). { apply list_lookup_lt. lia. } destruct H2 as [x0 Hx0].

          wp_pure; first lia.
          wp_apply (wp_load_slice_index with "[$Hxs2]") as "Hxs"; eauto; try lia.

          wp_pure; first lia.
          wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

          wp_apply "Hcmp". iIntros (r) "%Hcmp_r". wp_auto. wp_if_destruct. {
            (* write new data[j] *)
            wp_pure; first lia.
            wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

            wp_pure; first lia.
            wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

            (* write new data[j-1] *)
            wp_pure; first word.
            wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs". { iPureIntro; lia. }

            wp_pure; first word.
            wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs".
            { erewrite length_insert. iPureIntro. lia. }

            wp_for_post. iFrame. iPureIntro. split; first word. split_and!.
            - eapply perm_trans; eauto. eapply swap_perm; eauto.
            - unfold is_sorted_seg in *. intros.
              rewrite list_lookup_insert_ne in H3; try lia.
              rewrite list_lookup_insert_ne in H3; try lia.
              rewrite list_lookup_insert_ne in H4; try lia.
              rewrite list_lookup_insert_ne in H4; try lia.
              eapply Hsorted0; eauto.
            - eapply outside_same_trans; eauto.
              eapply outside_same_swap; lia.

          } {
            wp_for_post. iSplit; first auto. unfold HI.
            iFrame. auto.
          }

        } {
          iSplit; first auto. unfold HI. iFrame. auto.
        }
      } {
        iSplit; auto. unfold HI. iFrame. auto.
      }
    }
    iIntros (v) "[%Hv HI]". subst v. iNamed "HI". wp_for_post. iFrame. auto.
  } {
    iApply "HΦ"; iFrame; auto.
  }
Qed.

End proof.
