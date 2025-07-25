From Perennial.program_proof.tulip Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import util.

Definition sorted_u64 (ns : list u64) :=
  ∀ i j x y, (i ≤ j)%nat -> ns !! i = Some x -> ns !! j = Some y -> uint.Z x ≤ uint.Z y.

Lemma sorted_u64_snoc l1 n :
  sorted_u64 l1 ->
  Forall (λ x, uint.Z x ≤ uint.Z n) l1 ->
  sorted_u64 (l1 ++ [n]).
Proof.
  intros Hl1 Hle.
  intros i j x y Hij Hx Hy.
  rewrite lookup_snoc_Some in Hx.
  rewrite lookup_snoc_Some in Hy.
  destruct Hx as [[_ Hx] | [Hi Hxn]], Hy as [[Hlenl1 Hy] | [_ Hyn]].
  { apply (Hl1 _ _ _ _ Hij Hx Hy). }
  { subst n.
    rewrite Forall_forall in Hle.
    apply Hle.
    by apply list_elem_of_lookup_2 in Hx.
  }
  { lia. }
  { by subst x y. }
Qed.

Lemma sorted_u64_split l1 l2 :
  sorted_u64 (l1 ++ l2) ->
  sorted_u64 l1 ∧
  sorted_u64 l2 ∧
  (∀ x y, x ∈ l1 -> y ∈ l2 -> uint.Z x ≤ uint.Z y).
Proof.
  intros Hl12.
  rewrite /sorted_u64 in Hl12.
  split.
  { intros i j x y Hij Hx Hy.
    eapply Hl12.
    { apply Hij. }
    { rewrite lookup_app_l; first done.
      by eapply lookup_lt_Some.
    }
    { rewrite lookup_app_l; first done.
      by eapply lookup_lt_Some.
    }
  }
  split.
  { intros i j x y Hij Hx Hy.
    assert (Hlen : (i + length l1 ≤ j + length l1)%nat) by lia.
    eapply Hl12.
    { apply Hlen. }
    { rewrite lookup_app_r.
      { by rewrite Nat.add_sub. }
      (* lia is really weird when the goal involves length *)
      word.
    }
    { rewrite lookup_app_r.
      { by rewrite Nat.add_sub. }
      (* lia is really weird when the goal involes length *)
      word.
    }
  }
  { intros x y Hx Hy.
    apply list_elem_of_lookup in Hx as [i Hx].
    apply list_elem_of_lookup in Hy as [j Hy].
    assert (Hij : (i ≤ j + length l1)%nat).
    { apply lookup_lt_Some in Hx. word. }
    eapply Hl12.
    { apply Hij. }
    { rewrite lookup_app_l; first done.
      by eapply lookup_lt_Some.
    }
    rewrite lookup_app_r.
    { by rewrite Nat.add_sub. }
    word.
  }
Qed.

Lemma sorted_u64_combine l1 l2 :
  sorted_u64 l1 ->
  sorted_u64 l2 ->
  (∀ x y, x ∈ l1 -> y ∈ l2 -> uint.Z x ≤ uint.Z y) ->
  sorted_u64 (l1 ++ l2).
Proof.
  rewrite /sorted_u64.
  intros Hl1 Hl2 Hl12.
  intros i j x y Hij Hx Hy.
  destruct (decide (i < length l1)%nat) as [Hlt1 | Hge1].
  { rewrite lookup_app_l in Hx; last done.
    destruct (decide (j < length l1)%nat) as [Hlt2 | Hge2].
    { rewrite lookup_app_l in Hy; last done.
      by apply (Hl1 i j).
    }
    { rewrite lookup_app_r in Hy; last word.
      apply Hl12.
      { by apply list_elem_of_lookup_2 in Hx. }
      { by apply list_elem_of_lookup_2 in Hy. }
    }
  }
  { rewrite lookup_app_r in Hx; last word.
    destruct (decide (j < length l1)%nat) as [Hlt2 | Hge2].
    { lia. }
    { rewrite lookup_app_r in Hy; last word.
      eapply Hl2; [| apply Hx | apply Hy].
      lia.
    }
  }
Qed.

Section sort.
  Context `{!heapGS Σ}.

  Theorem wp_swap (nsP : Slice.t) (ns : list u64) (iW jW : u64) (x y : u64) :
    let i := uint.nat iW in
    let j := uint.nat jW in
    ns !! i = Some x ->
    ns !! j = Some y ->
    {{{ own_slice_small nsP uint64T (DfracOwn 1) ns }}}
      swap (to_val nsP) #iW #jW
    {{{ RET #(); own_slice_small nsP uint64T (DfracOwn 1) (<[j := x]> (<[i := y]> ns)) }}}.
  Proof.
    iIntros (i j Hx Hy Φ) "Hns HΦ".
    wp_rec.

    (*@ func swap(ns []uint64, i, j uint64) {                                   @*)
    (*@     tmp := ns[i]                                                        @*)
    (*@     ns[i] = ns[j]                                                       @*)
    (*@     ns[j] = tmp                                                         @*)
    (*@ }                                                                       @*)
    wp_apply (wp_SliceGet with "[$Hns]"); first done.
    iIntros "Hns".
    wp_apply (wp_SliceGet with "[$Hns]"); first done.
    iIntros "Hns".
    wp_apply (wp_SliceSet with "[$Hns]"); first done.
    iIntros "Hns".
    wp_apply (wp_SliceSet with "[$Hns]").
    { iPureIntro.
      rewrite lookup_lt_is_Some length_insert.
      by apply lookup_lt_Some in Hy.
    }
    iIntros "Hns".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_Sort (nsP : Slice.t) (ns : list u64) :
    {{{ own_slice nsP uint64T (DfracOwn 1) ns }}}
      Sort (to_val nsP)
    {{{ (ns' : list u64), RET #(); 
        own_slice nsP uint64T (DfracOwn 1) ns' ∗ ⌜sorted_u64 ns' ∧ ns' ≡ₚ ns⌝
    }}}.
  Proof.
    iIntros (Φ) "Hns HΦ".
    wp_rec.

    (*@ func Sort(ns []uint64) {                                                @*)
    (*@     var i uint64 = 1                                                    @*)
    (*@     for i < uint64(len(ns)) {                                           @*)
    (*@         var j uint64 = i                                                @*)
    (*@         for j > 0 {                                                     @*)
    (*@             if ns[j - 1] <= ns[j] {                                     @*)
    (*@                 break                                                   @*)
    (*@             }                                                           @*)
    (*@             swap(ns, j - 1, j)                                          @*)
    (*@             j--                                                         @*)
    (*@         }                                                               @*)
    (*@         i++                                                             @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply wp_ref_to; first by auto.
    iIntros (iP) "HiP".
    iDestruct (own_slice_small_acc with "Hns") as "[Hns HnsC]".
    iDestruct (own_slice_small_sz with "Hns") as %Hlenns.
    set P := (λ cont : bool, ∃ (ns' : list u64) (i : u64),
                 "Hns"      ∷ own_slice_small nsP uint64T (DfracOwn 1) ns' ∗
                 "HiP"      ∷ iP ↦[uint64T] #i ∗
                 "%Hperm"   ∷ ⌜ns' ≡ₚ ns⌝ ∗
                 "%Hsorted" ∷ ⌜sorted_u64 (take (uint.nat i) ns')⌝ ∗
                 "%Hbound"  ∷ ⌜if cont then True else (length ns ≤ uint.nat i)%nat⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [$Hns $HiP]"); last first; first 1 last.
    { iPureIntro.
      split; first done.
      split; last done.
      assert (uint.nat (W64 1) = 1%nat) as -> by word.
      intros i j x y Hij Hx Hy.
      apply lookup_take_Some in Hx as [Hx Hi].
      apply lookup_take_Some in Hy as [Hy Hj].
      assert (i = O) as -> by word.
      assert (j = O) as -> by word.
      rewrite Hx in Hy. by inv Hy.
    }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      iNamed "HP".
      wp_load.
      wp_apply wp_slice_len.
      wp_pures.
      case_bool_decide as Hi; wp_pures; last first.
      { iApply "HΦ". iFrame "∗ %". word. }
      wp_load.
      wp_apply wp_ref_to; first by auto.
      iIntros (jP) "HjP".
      assert (is_Some (ns' !! uint.nat i)) as [x Hx].
      { rewrite lookup_lt_is_Some Hperm. word. }
      apply take_drop_middle in Hx.
      rewrite cons_middle app_assoc in Hx.
      set nsleft := take _ _ in Hx Hsorted.
      set nsright := drop _ _ in Hx.
      set Q := (λ cont : bool, ∃ (jW : u64),
                   let j := uint.nat jW in
                   let nsleft' := take j nsleft ++ [x] ++ drop j nsleft in
                   "Hns"  ∷ own_slice_small nsP uint64T (DfracOwn 1) (nsleft' ++ nsright) ∗
                   "HjP"  ∷ jP ↦[uint64T] #jW ∗
                   "%Hij" ∷ ⌜uint.Z j ≤ uint.Z i⌝ ∗
                   "%Hlt" ∷ ⌜Forall (λ y, uint.Z x < uint.Z y) (drop j nsleft)⌝ ∗
                   "%Hge" ∷ ⌜(if cont
                              then True
                              else match last (take j nsleft) with
                                   | Some y => uint.Z y ≤ uint.Z x
                                   | None => True
                                   end)⌝)%I.
      wp_apply (wp_forBreak_cond Q with "[] [Hns $HjP]"); last first; first 1 last.
      { rewrite take_idemp -subslice_take_drop subslice_zero_length /= Hx.
        iFrame.
        iPureIntro.
        split; [word | done].
      }
      { clear Φ.
        iIntros (Φ) "!> HQ HΦ".
        iNamed "HQ".
        wp_load.
        wp_pures.
        case_bool_decide as Hj; wp_pures; last first.
        { iApply "HΦ".
          iFrame.
          iPureIntro.
          split; first done.
          split; first done.
          assert (uint.nat jW = O) as -> by word.
          by rewrite take_0 /=.
        }
        set j := uint.nat jW.
        set ns'' := _ ++ nsright.
        wp_load.
        assert (length (take j nsleft) = j) as Hlenj.
        { rewrite 2!length_take Hperm Hlenns. word. }
        assert (ns'' !! j = Some x) as Hx'.
        { subst ns''.
          rewrite lookup_app_l; last first.
          { rewrite length_app /= Hlenj. lia. }
          rewrite lookup_app_r; last first.
          { by rewrite Hlenj. }
          by rewrite Hlenj /= Nat.sub_diag.
        }
        set k := pred j.
        assert (is_Some (ns'' !! k)) as [y Hy].
        { rewrite lookup_lt_is_Some.
          subst ns''.
          rewrite 2!length_app Hlenj /=. lia.
        }
        wp_apply (wp_SliceGet with "[$Hns]").
        { iPureIntro.
          replace (uint.nat _) with (pred j) by word.
          apply Hy.
        }
        iIntros "Hns".
        wp_load.
        wp_apply (wp_SliceGet with "[$Hns]").
        { iPureIntro. apply Hx'. }
        iIntros "Hns".
        wp_pures.
        case_bool_decide as Hxy; wp_pures.
        { iApply "HΦ".
          iFrame.
          iPureIntro.
          split; first done.
          split; first done.
          subst ns''.
          rewrite lookup_app_l in Hy; last first.
          { rewrite length_app 2!length_take Hperm Hlenns /=. word. }
          rewrite lookup_app_l in Hy; last first.
          { rewrite 2!length_take Hperm Hlenns /=. word. }
          by rewrite last_lookup Hlenj Hy.
        }
        do 2 wp_load.
        wp_apply (wp_swap with "Hns").
        { replace (uint.nat _) with (pred j) by word.
          apply Hy.
        }
        { apply Hx'. }
        iIntros "Hns".
        wp_load.
        wp_store.
        iApply "HΦ".
        iFrame.
        replace (uint.nat (word.sub _ _)) with (pred j) by word.
        set nsx := insert _ _ _.
        set nsy := _ ++ nsright.
        assert (nsleft !! k = Some y) as Hy'.
        { subst ns''.
          rewrite lookup_app_l in Hy; last first.
          { rewrite length_app 2!length_take Hperm Hlenns /=. word. }
          rewrite lookup_app_l in Hy; last first.
          { rewrite 2!length_take Hperm Hlenns /=. word. }
          by apply lookup_take_Some in Hy as [? _].
        }
        assert (nsx = nsy) as ->.
        { subst nsx nsy ns''.
          rewrite insert_app_l; last first.
          { rewrite length_app Hlenj. word. }
          rewrite insert_app_l; last first.
          { rewrite length_insert 2!length_app /= Hlenj. word. }
          f_equal.
          rewrite insert_app_l; last first.
          { rewrite  Hlenj. word. }
          rewrite insert_app_r_alt; last first.
          { rewrite length_insert length_take. word. }
          rewrite length_insert Hlenj.
          rewrite insert_app_l; last first.
          { simpl. word. }
          replace (_ - _)%nat with O by word.
          simpl.
          rewrite -{2 3}(Nat.succ_pred j); last word.
          rewrite (take_S_r _ _ _ Hy').
          rewrite (insert_app_r_alt _ _ k); last first.
          { rewrite length_take. lia. }
          replace (_ - _)%nat with O; last first.
          { rewrite length_take. apply lookup_lt_Some in Hy'. lia. }
          simpl.
          rewrite (drop_S _ _ _ Hy').
          by rewrite -app_assoc.
        }
        iFrame.
        iPureIntro.
        split; first word.
        split; last done.
        rewrite (drop_S _ _ _ Hy').
        apply Forall_cons.
        split; last first.
        { replace (S k) with j by word. apply Hlt. }
        clear -Hxy. word.
      }
      iNamed 1.
      wp_load. wp_store.
      iApply "HΦ".
      iFrame.
      iPureIntro.
      split.
      { rewrite -Hperm -Hx.
        apply Permutation_app_tail.
        rewrite app_assoc app_Permutation_comm app_assoc.
        apply Permutation_app_tail.
        by rewrite app_Permutation_comm take_drop.
      }
      split; last done.
      rewrite uint_nat_word_add_S; last word.
      rewrite take_app_length'; last first.
      { rewrite app_assoc app_Permutation_comm app_assoc length_app /=.
        rewrite app_Permutation_comm take_drop length_take Hperm.
        clear -Hi Hlenns. lia.
      }
      rewrite -(take_drop (uint.nat jW) nsleft) in Hsorted.
      apply sorted_u64_split in Hsorted as (Hsortedl & Hsortedr & Hsortedlr).
      rewrite app_assoc.
      apply sorted_u64_combine.
      { apply sorted_u64_snoc; first apply Hsortedl.
        destruct (last _) as [z |] eqn:Hz; last first.
        { rewrite last_None in Hz. by rewrite Hz. }
        rewrite Forall_forall.
        intros w Hw.
        trans (uint.Z z); last apply Hge.
        rewrite last_lookup in Hz.
        apply list_elem_of_lookup_1 in Hw as [k Hw].
        rewrite /sorted_u64 in Hsortedl.
        eapply Hsortedl; last first.
        { apply Hz. }
        { apply Hw. }
        rewrite 2!length_take Hperm Hlenns.
        replace (uint.nat jW `min` _)%nat with (uint.nat jW) by word.
        clear -Hz Hw Hsortedl.
        apply lookup_take_Some in Hw as [_ Hlt].
        lia.
      }
      { apply Hsortedr. }
      intros z y Hz Hy.
      apply elem_of_app in Hz as [Hz | Hz].
      { by apply Hsortedlr. }
      rewrite Forall_forall in Hlt.
      specialize (Hlt _ Hy).
      apply list_elem_of_singleton in Hz as ->.
      lia.
    }
    iNamed 1.
    wp_pures.
    iDestruct ("HnsC" with "Hns") as "Hns".
    iApply "HΦ".
    iFrame.
    iPureIntro.
    split; last done.
    rewrite take_ge in Hsorted; first done.
    by rewrite Hperm.
  Qed.

End sort.
