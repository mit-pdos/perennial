From Goose.github_com.session Require Import sort.
From Perennial.program_proof Require Import std_proof. 
From Perennial.goose_lang.ffi.grove_ffi Require Export impl.
From Perennial.program_logic Require Export atomic.
From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.goose_lang.lib Require Import struct.struct into_val.
From RecordUpdate Require Import RecordSet.
From Perennial.goose_lang Require Import prelude.

Local Lemma Z_scope_test : (0%Z) + (0%Z) = 0%Z.
Proof. done. Qed.


Section heap.
  Context `{hG: !heapGS Σ}.

  Definition is_sorted (xs: list w64) :=
  ∀ (i j: nat), (i < j)%nat ->
         ∀ (x1 x2: w64), xs !! i = Some x1 ->
                         xs !! j = Some x2 ->
                         uint.Z x1 <= uint.Z x2.

  Definition is_sorted_eq (xs: list w64) := 
  ∀ (i j: nat), (i <= j)%nat ->
         ∀ (x1 x2: w64), xs !! i = Some x1 ->
                         xs !! j = Some x2 ->
                         uint.Z x1 <= uint.Z x2.

  Lemma sorted_eq (l: list w64) :
    is_sorted l -> is_sorted_eq l.
  Proof.
    unfold is_sorted.
    intros.
    unfold is_sorted_eq.
    intros.
    destruct (decide (i = j)).
    - rewrite e in H1. rewrite H2 in H1. injection H1 as ?. word.
    - eapply H.
      + assert (i < j)%nat by word. apply H3.
      + eassumption.
      + eassumption.
  Qed.

  (* Allow for it to take in a higher order function *)
  Lemma implies_Sorted :
    forall (xs: list w64) (element: w64) (i: w64),
    is_sorted xs ->
    uint.nat i <= length xs ->
    (∀ (i': nat), i' < uint.nat i →
                  ∀ (x: w64), xs !! i' = Some x →
                              uint.Z x < uint.Z element) -> 
    (∀ (j': nat),
          uint.nat i ≤ j' →
          ∀ (y: w64), xs !! j' = Some y →
                      uint.Z element <= uint.Z y) ->
    is_sorted ((take (uint.nat i) xs) ++ (cons element (drop (uint.nat i) xs))).
  Proof.
    unfold is_sorted. intros.
    destruct (decide (j < uint.nat i)).
    - assert (i0 < (uint.nat i - 1)) by word.
      rewrite lookup_app_l in H4.
      + rewrite lookup_app_l in H5.
        * rewrite lookup_take in H4; try word.
          rewrite lookup_take in H5; try word.
          eapply H in H3; try eassumption.
        * rewrite length_take_le; try word.
      + rewrite length_take_le; try word.
    - assert (j >= (uint.nat i - 1)) by word. clear n.
      destruct (decide (j = (uint.nat i)%nat)).
      + clear H6. subst.
        (* H5: element = Some x2 *)
        rewrite lookup_app_l in H4.
        * rewrite lookup_app_r in H5.
          -- rewrite length_take_le in H5; try word.
             assert ((uint.nat i - (uint.nat i))%nat = 0%nat) by word.
             rewrite H6 in H5. rewrite <- head_lookup in H5. simpl in H5.
             injection H5 as ?. rewrite lookup_take in H4; try word. 
             assert (i0 < uint.nat i) by word. rewrite <- H5.
             apply Z.lt_le_incl. eapply H1; try eassumption.
          -- rewrite length_take_le; try word.
        * rewrite length_take_le; try word.
      + destruct (decide (i0%nat = (uint.nat i))).
        * assert (j > uint.nat i) by word. rewrite lookup_app_r in H4.
        -- rewrite lookup_app_r in H5.
           ++ rewrite e in H4. rewrite length_take_le in H4; try word.
              assert ((uint.nat i - uint.nat i)%nat = 0%nat) by word.
              rewrite H8 in H4. rewrite <- head_lookup in H4. simpl in H4.
              injection H4 as ?. rewrite <- H4.
              rewrite lookup_cons_ne_0 in H5; try rewrite length_take_le; try word.
              rewrite lookup_drop in H5. eapply H2.
              ** assert (uint.nat i <= (uint.nat i + Init.Nat.pred (j - length (take (uint.nat i) xs)))%nat) by word. apply H9. 
              ** auto. 
           ++ rewrite length_take_le; try word.
        -- rewrite length_take_le; try word.
        * destruct (decide (i0%nat > (uint.nat i))).
          -- clear n0. clear n.
             rewrite lookup_app_r in H4; try rewrite length_take_le; try word.
             rewrite lookup_app_r in H5; try rewrite length_take_le; try word.
             rewrite lookup_cons_ne_0 in H4; try rewrite length_take_le; try word.
             rewrite lookup_cons_ne_0 in H5; try rewrite length_take_le; try word.
             rewrite lookup_drop in H4. rewrite lookup_drop in H5.
             rewrite length_take_le in H4; try word.
             rewrite length_take_le in H5; try word.
             eapply H.
             ++ assert (Init.Nat.pred (i0 - uint.nat i) <Init.Nat.pred (j - uint.nat i)) by word.
                assert (uint.nat i + Init.Nat.pred (i0 - uint.nat i) <
                          uint.nat i + Init.Nat.pred (j - uint.nat i))%nat by word.
                apply H8.
             ++ auto.
             ++ auto.
          -- assert (i0 < uint.nat i) by word.
             destruct (decide (j = (uint.nat i - 1)%nat)).
             ++ rewrite lookup_app_l in H4; try rewrite length_take_le; try word.
                rewrite lookup_app_l in H5; try rewrite length_take_le; try word.
                rewrite lookup_take in H4; try word.
                rewrite lookup_take in H5; try word.
                eapply H in H3; try eassumption.
             ++ assert (j > uint.nat i) by word.
                rewrite lookup_app_l in H4; try rewrite length_take_le; try word.
                rewrite lookup_app_r in H5; try rewrite length_take_le; try word.
                rewrite lookup_cons_ne_0 in H5; try rewrite length_take_le;
                  try word.
                rewrite lookup_take in H4; try word.
                rewrite lookup_drop in H5. eapply H.
                ** assert (i0 < (uint.nat i + Init.Nat.pred (j - length (take (uint.nat i) xs)))%nat)%nat by word. apply H9.
                ** auto.
                ** auto.
  Qed.
    
  Lemma wp_BinarySearch (s: Slice.t) (xs: list w64) (needle: w64) :
  {{{ own_slice s uint64T (DfracOwn 1) xs ∗ ⌜is_sorted xs⌝ }}}
    BinarySearch s #needle
  {{{ (i: w64) (ok: bool), RET (#i, #ok);
      own_slice s uint64T (DfracOwn 1) xs ∗
      ⌜ok = true → xs !! uint.nat i = Some needle⌝ ∗
      ⌜is_sorted xs⌝ ∗
      ⌜ ∀ (i': nat), i' < uint.nat i →
                   ∀ (x: w64), xs !! i' = Some x →
                               uint.Z x < uint.Z needle⌝ ∗
      ⌜∀ (j': nat),
                   uint.nat i ≤ j' →
                   ∀ (y: w64), xs !! j' = Some y →
                               uint.Z needle <= uint.Z y⌝ ∗
                               ⌜uint.nat i <= length xs⌝
  }}}.
  Proof.
    iIntros (Φ) "H H1". unfold BinarySearch.
    wp_pures.
    wp_apply wp_ref_to; auto.
    iIntros (i_l) "i". wp_pures.
    wp_apply wp_slice_len.
    wp_apply wp_ref_to; auto.
    iIntros (j_l) "j". wp_pures.
    iDestruct "H" as "(H & %H2)".
    iDestruct "H" as "(H & H3)". 
    iDestruct (own_slice_small_sz with "H") as %Hsz.
    wp_apply (wp_forBreak_cond
                (λ continue, ∃ (i j: w64),
                    own_slice s uint64T (DfracOwn 1) xs ∗
                    i_l ↦[uint64T] #i ∗
                    j_l ↦[uint64T] #j ∗
                    ⌜uint.Z i ≤ uint.Z j ≤ Z.of_nat (length xs)⌝ ∗
                    ⌜∀ (i': nat),
                   i' < uint.nat i →
                   ∀ (x: w64), xs !! i' = Some x →
                               uint.Z x < uint.Z needle⌝ ∗
                               ⌜∀ (j': nat),
                   uint.nat j ≤ j' →
                   ∀ (y: w64), xs !! j' = Some y →
                               uint.Z needle <= uint.Z y⌝ ∗
                               ⌜continue = false → i = j⌝ ∗
                               ⌜uint.nat i <= length xs⌝ 
                )%I
               with "[] [H H3 i j]").
    - iIntros (?). iModIntro. iIntros "H1 H2".
      wp_pures. iNamed "H1". iDestruct "H1" as "(H3 & H4 & H5 & %H6 & %H7 & %H8 & %H9)".
      wp_load. wp_load.
      wp_if_destruct.
      + wp_pures.
        wp_load. wp_load. wp_load. wp_pures.
        set (mid := word.add i (word.divu (word.sub j i) (W64 2)) : w64).
        assert (uint.Z mid = (uint.Z i + uint.Z j) / 2) as Hmid_ok.
        { subst mid.
          word. }
        list_elem xs (uint.nat mid) as x_mid.
        iDestruct "H3" as "(H3 & H6)".
        wp_apply (wp_SliceGet with "[$H3]").
        { eauto. }
        iIntros "Hs".
        simpl to_val.
        wp_pures.
        wp_if_destruct.
        * wp_store.
          iModIntro.
          iApply "H2".
          iExists (W64 (uint.Z mid + 1)). 
          iFrame.
          iSplitL.
          { unfold mid. 
            iPureIntro.
            split_and!; try word.
          }
          unfold is_sorted in *.
          iPureIntro. split.
          { intros.
            assert (i' ≤ uint.nat mid)%nat by word.
            destruct (decide ((i' < uint.nat mid)%nat)).
            - apply (H2 i' (uint.nat mid) l x x_mid) in H0; try eassumption.
              word.
            - assert (i' = uint.nat mid) by word. rewrite <- H3 in Hx_mid_lookup.
              rewrite Hx_mid_lookup in H0. injection H0 as ?. word.
          } 
          split.
          { intros. eapply H8; try apply H. auto. }
          { split.
            - intros. inversion H.
            - word. }
        * wp_store.
          iModIntro.
          iApply "H2".
          iExists i.
          iExists mid.
          iFrame.
          iPureIntro.
          split_and!; try word.
          { auto. }
          intros. unfold is_sorted in *. assert (uint.Z needle <= uint.Z x_mid ) by word.
          clear Heqb0. 
          destruct (decide (uint.nat mid = j')).
          { rewrite e in Hx_mid_lookup. rewrite H0 in Hx_mid_lookup. inversion Hx_mid_lookup.
            auto.
          } 
          { assert (uint.nat mid < j')%nat by word. assert (uint.Z x_mid <= uint.Z y). {
              eapply H2.
              - apply H3.
              - auto.
              - auto.
            } etrans; try eassumption.
          }
      + iModIntro.
        iApply "H2".
        iFrame.
        iPureIntro.
        split_and!; try word; auto.
        intros.
        word.
    - iFrame. iPureIntro.
      split; try word.
      split; try word. split.
      + intros. apply lookup_lt_Some in H0. word.
      + word.
    - iIntros "Hpost".
      wp_pures. iNamed "Hpost". iDestruct "Hpost" as "(H2 & H3 & H4 & %H5 & %H6 & %H7 & %H8 & %H9)".
      wp_load. wp_pures. wp_apply wp_slice_len. rewrite Hsz. wp_pures.
      wp_if_destruct.
      + assert (uint.Z i < uint.nat s.(Slice.sz)) by word. rewrite <- Hsz in H.
        assert (uint.nat i < length xs)%nat by word.
        eapply list_lookup_lt in H0.
        wp_load. wp_bind (SliceGet _ _ _)%E.
        wp_load.
        iDestruct "H2" as "(H9 & H10)".
        assert (uint.Z i < uint.nat s.(Slice.sz)) by word.
        rewrite <- Hsz in H1.
        assert (uint.nat i < length xs)%nat by word.
        eapply list_lookup_lt in H3.
        destruct H3.
        wp_apply (wp_SliceGet with "[$H9]").
        * assert (uint.Z i < uint.nat s.(Slice.sz)) by word. iPureIntro. 
          apply H3.
        * iIntros "H". wp_pures. iModIntro. iApply "H1". iFrame. iPureIntro. split.
          -- destruct (decide (#x = #needle)). 
             ++ intros. apply bool_decide_eq_true in H4. inversion H4. rewrite <- H11. auto.
             ++ intros. apply bool_decide_eq_true in H4. inversion H4. rewrite <- H11. auto.
          -- split; auto. split.
             { intros. eapply H6 in H4; eassumption. }
             { intros. destruct H8; auto. split; try word. 
               eapply H7; eassumption. }
      + wp_load. wp_pures. iModIntro. iApply "H1". iFrame. iPureIntro. intros. split; try intros;
          try inversion H. split; auto. split.
        { intros. eapply H6; eassumption. }
        { intros. destruct H8; auto. split; try word. eapply H7; eassumption. }
  Qed.

  Lemma cons_append (A: Type) (x: list A) (e : A):
    [e] ++ x = cons e x.
  Proof.
    induction x.
    - auto.
    - simpl. auto.
  Qed.

  
  Fixpoint insert (l : list w64) (i : w64) :=
    match l with
    | [] => [i]
    | cons h t => if uint.Z i <=? uint.Z h then (i :: h :: t)%list else (h :: insert t i)%list
    end.
  
  Lemma wp_insert (s: Slice.t) (xs: list w64) (v: w64) :
    {{{ own_slice s uint64T (DfracOwn 1) xs ∗ ⌜is_sorted xs⌝ }}}
      sortedInsert s #v
      {{{ (ns: Slice.t), RET slice_val (ns);
          (∃ (nxs: list w64), own_slice ns uint64T (DfracOwn 1) nxs ∗
                              ⌜is_sorted nxs⌝ ∗ ⌜Permutation nxs (v :: xs)%list⌝)%I
      }}}.
  Proof.
    iIntros (Φ) "(H & %H1) H2". unfold sortedInsert. wp_pures. 
    wp_apply (wp_BinarySearch with "[$H]"); auto.
    iIntros (i ok) "(H & %H &%H3 & %H4 & %H5 & %H6)". wp_pures.
    iDestruct (own_slice_sz with "H") as %Hsz.
    unfold slice.len. wp_pures.
    wp_if_destruct.
    - wp_apply (wp_SliceAppend with "[$]").
      iIntros (s') "H".
      iApply "H2".
      iExists (xs ++ [v]).
      iFrame.
      iPureIntro.
      apply (implies_Sorted xs v (length xs)) in H3; try word.
      + assert ((take (uint.nat (W64 (length xs))) (xs ++ []) ++ v :: drop (uint.nat (W64 (length xs))) (xs ++ []) ) = (xs ++ [v])). {
          replace (uint.nat (W64 (length xs))) with (length xs)%nat by word.
          rewrite take_app_length. rewrite drop_app_length. auto. }
        rewrite app_nil_r in H0. rewrite <- H0. auto. split; try auto.
        rewrite H0. assert ((v :: xs)%list = [v] ++ xs) by auto.
        symmetry. apply Permutation_cons_append. 
      + replace (uint.nat (W64 (length xs))) with (length xs)%nat by word. rewrite Hsz.
        auto.
      + replace (uint.nat (W64 (length xs))) with (length xs)%nat by word. rewrite Hsz.
        auto.
    - wp_bind (SliceAppendSlice _ _ _).
      wp_apply wp_SliceSkip; try word.
      unfold own_slice.
      unfold slice.own_slice.
      iDestruct (own_slice_wf with "H") as %Hcap.
      iDestruct "H" as "[H H1]".
      iDestruct (slice_small_split with "H") as "H".
      + assert (uint.Z i <= length xs) by word.
        apply H0.
      + iDestruct "H" as "[H H3]".
        wp_apply slice.wp_SliceSingleton; auto.
        iIntros (s0) "H4".
        wp_apply (wp_SliceAppendSlice with "[H3 H4]"); try auto.
        * unfold own_slice. iSplitL "H4".
          -- assert (list.untype [#v] = cons #v []). {
               auto.
             }
             rewrite <- H0. iFrame.
          -- iFrame. 
        * iIntros (s') "[H3 H4]". wp_pures. wp_bind (SliceAppendSlice _ _ _).
          wp_apply wp_SliceTake; try word.
          wp_apply (wp_SliceAppendSlice with "[H H1 H3 H4]"); try auto.
          -- iAssert (own_slice_small (slice_skip s uint64T i) uint64T (DfracOwn 1) (drop (uint.nat i) xs) ∗ own_slice_cap s uint64T)%I with "[H1 H4]" as "H5". { iFrame. }
             iApply own_slice_cap_take in "H5"; try word.
             iFrame. unfold own_slice. unfold slice.own_slice. unfold own_slice_small.
             iDestruct "H3" as "[H3 H4]". iFrame.
          -- iIntros (s'0) "H". wp_pures. iModIntro. iApply "H2".
             iExists (take (uint.nat i) xs ++ [#v] ++ drop (uint.nat i) xs).
             iDestruct "H" as "[H H1]".
             iSplitL.
             ++ unfold own_slice. unfold slice.own_slice. iDestruct "H" as "[H H2]".
                iFrame.
             ++ iPureIntro. apply (implies_Sorted xs v (uint.nat i)) in H3; try word.
                ** assert ((take (uint.nat (W64 (uint.nat i))) xs ++ v :: drop (uint.nat (W64 (uint.nat i))) xs) = (take (uint.nat i) xs ++ [#v] ++ drop (uint.nat i) xs)). {
                     replace (uint.nat (W64 (uint.nat i))) with (uint.nat i)%nat by word.
                     rewrite cons_append. auto.
                   }
                   rewrite <- H0. auto. split; try auto. rewrite H0.
                   rewrite Permutation_app_swap_app. rewrite take_drop.
                   symmetry. auto.
                ** replace (uint.nat (W64 (uint.nat i))) with (uint.nat i)%nat by word.
                   apply H4.
                ** replace (uint.nat (W64 (uint.nat i))) with (uint.nat i)%nat by word.
                   apply H5.
  Qed.

  Fixpoint insert (l : list w64) (i : w64) :=
    match l with
    | [] => [i]
    | cons h t => if uint.Z i <=? uint.Z h then (i :: h :: t)%list else (h :: insert t i)%list
    end.

  Definition is_a_sorted_insert_algorthim (f: list w64 -> w64 -> list w64) := ∀ l e,
      Permutation (e :: l)%list (f l e) ∧ is_sorted (f l e).

  Lemma proof_insert :
    is_a_sorted_insert_algorthim insert.
  Proof.
    unfold is_a_sorted_insert_algorthim.
    intros. split.
    - unfold insert. induction l; try auto.
      destruct (decide (uint.Z e <=? uint.Z a = true)).
      + rewrite e0. auto.
      + assert ((uint.Z e <=? uint.Z a = false)) by word.
        rewrite H. admit.
  Admitted.

  
  Lemma impl xs ys :
    Permutation xs ys ->
    is_sorted xs ->
    is_sorted ys ->
    xs = ys.
  Proof.
    intros.
    apply list_eq.
    intros. unfold is_sorted in *.
    induction 

    
                

(* TODO:
   Define a sorting function,
   prove that if two lists are permutations,
   then they satisfy is_sorted
 *)

Inductive sorted: list w64 → Prop :=
| sorted_nil: sorted []
| sorted_1: ∀ i, sorted [i]
| sorted_cons: ∀ i j l, uint.Z i ≤ uint.Z j → sorted (j :: l) → sorted (i :: j :: l).

(* There are two places which we require sorting in each case it is with respect to
   a comparision function 
 *)

Lemma sorted_equiv (l: list w64) :
  is_sorted l <-> sorted l.
Proof.
  split.
  - intros.
    induction l.
    + apply sorted_nil.
    + unfold is_sorted in *.
      destruct l.
      * apply sorted_1.
      * apply sorted_cons.
        { eapply H.
          - assert (0 < 1)%nat by lia. apply H0.
          - auto.
          - auto.
        }
        apply IHl. intros. assert (S i < S j)%nat by word. eapply H in H3.
        { apply H3. }
        { rewrite lookup_cons. auto. }
        { rewrite lookup_cons. auto. }
  - intros.
    induction l.
    + unfold is_sorted. intros. inversion H1.
    + unfold is_sorted in *.
      intros.
Admitted.


Lemma impl f h l :
  is_sorted f ->
  is_sorted h ->
  
            

Definition is_a_sorting_algorithm (f: list w64 → list w64) := ∀ al,
    Permutation al (f al) ∧ is_sorted (f al).

Lemma impl f h l :
  is_a_sorting_algorithm f ->
  is_a_sorting_algorithm h ->
  f l = h l.
Proof. 
  intros. unfold is_a_sorting_algorithm in *.
  induction l.
  - specialize H with [].
    specialize H0 with [].
    destruct H.
    destruct H0.
    apply Permutation_nil_l in H0.
    apply Permutation_nil_l in H.
    rewrite <- H. rewrite <- H0. auto.
  - apply list_eq. intros.
    specialize H with (a :: l)%list.
    specialize H0 with (a :: l)%list.
    destruct H.
    destruct H0.
    unfold is_sorted in *.
    
    

    
    (* Prove that sorting gives a unique order *)
    (* every total order results in a unique result *)
    
  
                         


Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | cons h t => if i <=? h then cons i h :: t else h :: insert i t
  end.
Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] =? []
  | h :: t => insert h (sort t)
  end.
      
  
  
  




End heap. 
