From Perennial.Helpers Require Import List ModArith.

From Goose.github_com.goose_lang Require Import std.

From iris.algebra Require Import excl gset.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import typed_slice.

Class multiparG Σ : Set :=
   { multiparG_auth :> inG Σ (gset_disjR nat);
     multiparG_tok :> inG Σ (exclR unitO) }.
Definition multiparΣ := #[GFunctor (gset_disjR nat); GFunctor (exclR unitO)].
Global Instance subG_multiparΣ {Σ} :
  subG multiparΣ Σ → multiparG Σ.
Proof. solve_inG. Qed.

Section goose_lang.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.

Implicit Types (v:val).

Local Lemma take_S_lookup_ne {T} (xs : list T) i j :
  i ≠ j →
  take (S i) xs !! j = take i xs !! j.
Proof.
  destruct (le_lt_dec i j) as [Hle|Hlt].
  - intros ?. rewrite lookup_take_ge; last by lia.
    rewrite lookup_take_ge; last by lia. done.
  - rewrite lookup_take. 2:lia.
    rewrite lookup_take. 2:lia.
    done.
Qed.

Lemma inv_litint (i1 i2: w64) :
  #i1 = #i2 ↔ i1 = i2.
Proof.
  split; [ | congruence ].
  inversion 1; auto.
Qed.

Lemma wp_BytesEqual (x y : Slice.t) (xs ys : list byte) qx qy :
  {{{ own_slice_small x byteT qx xs ∗
      own_slice_small y byteT qy ys }}}
    BytesEqual (slice_val x) (slice_val y)
  {{{ RET #(bool_decide (xs = ys));
      own_slice_small x byteT qx xs ∗
      own_slice_small y byteT qy ys }}}.
Proof.
  iIntros (Φ) "[Hx Hy] HΦ". wp_lam. wp_pures.
  do 2 wp_apply wp_slice_len.
  wp_pures.
  iDestruct (own_slice_small_sz with "Hx") as %Hxlen.
  iDestruct (own_slice_small_sz with "Hy") as %Hylen.
  rewrite -bool_decide_not.
  destruct_decide (bool_decide_reflect (#x.(Slice.sz) ≠ #y.(Slice.sz))) as Hlen; wp_pures.
  { (* Different lengths. *)
    rewrite bool_decide_false.
    { iModIntro. iApply ("HΦ" with "[$]"). }
    intros <-.
    contradiction Hlen.
    do 2 f_equal.
    word. }
  wp_pures.
  apply inv_litint in Hlen.
  assert (length xs = length ys) as Hlens by congruence.

  wp_apply wp_ref_to; first by val_ty.
  iIntros (l) "Hi". wp_pures.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (ret) "Hret". wp_pures.

  iApply (wp_frame_wand with "HΦ").

  (* Weaken for loop invariant *)
  iAssert (∃ i : w64, l ↦[uint64T] #i ∗
                      ret ↦[boolT] #(bool_decide (take (uint.nat i) xs = take (uint.nat i) ys)))%I
    with "[Hi Hret]" as "Hinv".
  { iExists _. by iFrame. }

  wp_apply (wp_forBreak_cond' with "[-]"); first by iNamedAccu.
  iIntros "!# HP". iNamed "HP".
  iDestruct "Hinv" as (i) "[Hi Hret]".
  wp_pures.
  wp_load.
  wp_if_destruct; last first.
  { (* i >= length *)
    iModIntro.
    iRight. iSplit; first done. wp_load.
    iIntros "!> HΦ". iDestruct ("HΦ" with "[$Hx $Hy]") as "HΦ".
    iExactEq "HΦ".
    repeat f_equal.
    apply bool_decide_ext.
    rewrite take_ge; [ | len ].
    rewrite take_ge; [ | len ].
    auto. }
  wp_pures.
  destruct (lookup_lt_is_Some_2 xs (uint.nat i)) as [xi Hxi]; first word.
  destruct (lookup_lt_is_Some_2 ys (uint.nat i)) as [yi Hyi]; first word.
  wp_load.
  (* FIXME: some typeclass is set up wrong so TC inference picks the wrong type here *)
  wp_apply (wp_SliceGet (V:=u8) with "[$Hx]").
  { eauto. }
  iIntros "Hx".
  wp_load.
  wp_apply (wp_SliceGet (V:=u8) with "[$Hy]").
  { eauto. }
  iIntros "Hy".
  wp_pures.
  wp_if_destruct.
  - (* this index is inequal *)
    wp_store. iModIntro. iRight. iSplit; first done.
    wp_load. iModIntro.
    case_bool_decide as Heq.
    + exfalso. apply Heqb0. do 2 f_equal.
      apply Some_inj. rewrite -Hxi -Hyi Heq. done.
    + iIntros "HΦ". iApply "HΦ". eauto with iFrame.
  - (* this index is equal *)
    wp_load. wp_store.
    iModIntro. iLeft. iSplit; first done.
    iFrame "Hx Hy". iExists (word.add i (W64 1)).
    iFrame "Hi".
    iExactEq "Hret".
    repeat f_equal.
    apply bool_decide_ext.
    word_cleanup.
    replace (Z.to_nat (uint.Z i + 1)) with (S (uint.nat i)) by word.
    erewrite take_S_r by eauto.
    erewrite take_S_r by eauto.
    split; [ congruence | ].
    intros Heq.
    apply app_inv_tail in Heq; auto.
Qed.

Lemma wp_BytesClone sl_b q (b : list u8) :
  {{{
    own_slice_small sl_b byteT q b
  }}}
  BytesClone (slice_val sl_b)
  {{{
    sl_b0, RET (slice_val sl_b0);
    own_slice_small sl_b0 byteT (DfracOwn 1) b
  }}}.
Proof.
  iIntros (Φ) "Hsl_b HΦ".
  rewrite /BytesClone.
  wp_pures.
  wp_pure1; [done|].
  wp_if_destruct.
  {
    iIntros "!>".
    iSpecialize ("HΦ" $! Slice.nil).
    iApply "HΦ".
    inversion Heqb0.
    apply (f_equal uint.Z) in H1.
    iPoseProof (slice.own_slice_small_nil _ (DfracOwn 1)) as "Hsl_b'"; [done|].
    iDestruct (own_slice_small_agree with "[$Hsl_b] [$Hsl_b']") as %Heq.
    destruct b; [|done].
    iApply own_slice_to_small.
    iApply own_slice_zero.
  }
  {
    wp_apply wp_NewSlice.
    iIntros (sl_b0) "Hsl_b0".
    replace (uint.nat 0) with (0%nat) by word.
    wp_apply (wp_SliceAppendSlice with "[$Hsl_b $Hsl_b0]"); [done|].
    iIntros (?) "[Hs' _]".
    iDestruct (own_slice_to_small with "Hs'") as "Hs'".
    by iApply "HΦ".
  }
Qed.

Lemma wp_SliceSplit s dq (xs: list w8) (n: w64) :
  {{{ own_slice_small s byteT dq xs ∗ ⌜uint.Z n < Z.of_nat (length xs)⌝ }}}
    SliceSplit (to_val s) #n
  {{{ RET (to_val (slice_take s n), to_val (slice_skip s byteT n));
      own_slice_small (slice_take s n) byteT dq (take (uint.nat n) xs) ∗
      own_slice_small (slice_skip s byteT n) byteT dq (drop (uint.nat n) xs)
  }}}.
Proof.
  iIntros (Φ) "[Hs %Hn] HΦ".
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  iDestruct (own_slice_small_wf with "Hs") as %Hcap.
  wp_call.
  wp_apply wp_SliceTake.
  { word. }
  wp_apply wp_SliceSkip.
  { word. }
  wp_pures. iModIntro. iApply "HΦ".
  iDestruct (slice_small_split with "Hs") as "[$ $]".
  word.
Qed.

Lemma wp_SumNoOverflow (x y : u64) :
  ∀ Φ : val → iProp Σ,
    Φ #(bool_decide (uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z)) -∗
    WP SumNoOverflow #x #y {{ Φ }}.
Proof.
  iIntros (Φ) "HΦ".
  rewrite /SumNoOverflow. wp_pures.
  iModIntro. iExactEq "HΦ".
  repeat f_equal.
  apply bool_decide_ext.
  pose proof (sum_overflow_check x y).
  destruct (decide (uint.Z x ≤ uint.Z (word.add x y))); intuition idtac.
  - word.
  - word.
Qed.

Lemma wp_SumAssumeNoOverflow (x y : u64) :
  ∀ Φ : val → iProp Σ,
    (⌜uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z⌝ -∗ Φ #(LitInt $ word.add x y)) -∗
    WP SumAssumeNoOverflow #x #y {{ Φ }}.
Proof.
  iIntros "%Φ HΦ". wp_lam; wp_pures.
  wp_apply wp_SumNoOverflow.
  wp_apply wp_Assume.
  rewrite bool_decide_eq_true.
  iIntros (H). wp_pures. iModIntro.
  iApply "HΦ"; done.
Qed.

(* We pass some "ghost data" from [elems] to each invocation; [length elems] determines
   how many threads there are. *)
Lemma wp_Multipar `{!multiparG Σ} {X:Type} (P Q : nat → X → iProp Σ) (num:u64) (elems : list X) (op : val) :
  length elems = uint.nat num →
  □(∀ (i : u64) x, ⌜elems !! uint.nat i = Some x⌝ -∗ P (uint.nat i) x -∗ WP op #i {{ _, Q (uint.nat i) x }}) -∗
  {{{ [∗ list] i ↦ x ∈ elems, P i x }}}
    Multipar #num op
  {{{ RET #(); [∗ list] i ↦ x ∈ elems, Q i x }}}.
Proof.
  iIntros "%Hlen #Hop !> %Φ HPs HΦ". wp_lam.
  wp_apply wp_ref_to. { val_ty. }
  iIntros (nleft_l) "Hnleft". wp_pures.
  iMod (own_alloc (GSet (set_seq 0 (length elems)))) as (γpending) "Hpending".
  { done. }
  iMod (own_alloc (Excl ())) as (γtok) "Htok".
  { done. }
  set lock_inv := ( (∃ nleft : u64, nleft_l ↦[uint64T] #nleft ∗ own γtok (Excl ())) ∨
    ∃ (nleft : u64) (pending : gset nat),
      "%Hsz" ∷ ⌜size pending = uint.nat nleft⌝ ∗
      "Hnleft" ∷ nleft_l ↦[uint64T] #nleft ∗
      "HPQ" ∷ ([∗ list] i ↦ x ∈ elems, ⌜i ∈ pending⌝ ∨ own γpending (GSet {[i]}) ∗ Q i x)
      )%I.
  wp_apply (newlock_spec nroot _ lock_inv with "[Hnleft]").
  { iModIntro. rewrite /lock_inv. iRight.
    iExists num, (set_seq 0 (uint.nat num)). iFrame. iSplit.
    - iPureIntro. rewrite -list_to_set_seq size_list_to_set ?seq_length //.
      apply NoDup_seq.
    - iApply big_sepL_intro. iIntros "!> %k %i %Hlk". iLeft. iPureIntro.
      apply elem_of_set_seq. split; first lia.
      rewrite -Hlen. apply lookup_lt_is_Some_1. eauto. }
  iIntros (lk) "#Hlk". wp_pures.
  wp_apply (wp_newCond with "Hlk").
  iIntros (cond) "#Hcond". wp_pures.
  (* Loop starts *)
  wp_apply wp_ref_to. { val_ty. }
  iIntros (i_l) "Hi".
  set loop_inv := (λ cur : u64,
    [∗ list] i ↦ x ∈ drop (uint.nat cur) elems, own γpending (GSet {[(uint.nat cur)+i]}) ∗ P ((uint.nat cur)+i) x)%I%nat.
  wp_apply (wp_forUpto loop_inv _ _ 0 with "[] [HPs Hpending Hi]").
  { word. }
  { clear Φ.
    iIntros "%cur !> %Φ (Hloop & Hcur & %Hcur) HΦ". wp_pures.
    wp_load.
    assert (is_Some (elems !! uint.nat cur)) as [x Hx].
    { apply lookup_lt_is_Some. word. }
    iAssert (loop_inv (word.add cur 1) ∗ own γpending (GSet {[uint.nat cur]}) ∗ P (uint.nat cur) x)%I with "[Hloop]"
      as "(Hloop & Hpending & HP)".
    { rewrite /loop_inv.
      rewrite (drop_S _ _ _ Hx).
      simpl. rewrite Nat.add_0_r.
      iDestruct "Hloop" as "(($ & $) & Hloop)".
      replace (uint.nat (word.add cur 1)) with (S (uint.nat cur)) by word.
      setoid_rewrite Nat.add_succ_r. done. }
    wp_apply (wp_fork with "[HP Hpending]").
    { iModIntro. wp_bind (op _). iApply (wp_wand with "[HP]").
      { iApply "Hop"; done. }
      iIntros (_v) "HQ". wp_pures. clear _v.
      wp_apply (acquire_spec with "Hlk").
      iIntros "(Hlocked & [Hinv|Hinv])".
      { (* supposedly the main thread already removed all the resources...
           this cannot really happen, but we just go along with it. *)
        iDestruct "Hinv" as (nleft) "(Hnleft & Htok)".
        wp_load. wp_store.
        wp_apply (wp_condSignal with "Hcond").
        wp_apply (release_spec with "[$Hlocked $Hlk Hnleft Htok]"); last done.
        iLeft. eauto with iFrame. }
      iNamed "Hinv".
      wp_load. wp_store.
      wp_apply (wp_condSignal with "Hcond").
      wp_apply (release_spec with "[-]"); last done. iFrame "Hlocked Hlk".
      iRight. iExists _, (pending ∖ {[uint.nat cur]}). iFrame "Hnleft".
      iDestruct (big_sepL_lookup_acc_impl (uint.nat cur) with "HPQ") as "[Hcur Hclose]".
      { done. }
      iFreeze "Hclose".
      iDestruct "Hcur" as "[%Hpending|[Hpending2 _]]"; last first.
      { (* This index is supposedly already done -- contradiction. *)
        iDestruct (own_valid_2 with "Hpending Hpending2") as %Hval%gset_disj_valid_op.
        exfalso. set_solver. }
      iModIntro. iSplit.
      { iPureIntro. rewrite size_difference; last set_solver.
        rewrite Hsz size_singleton.
        assert (uint.nat nleft ≠ 0%nat). 2:word.
        rewrite -Hsz. intros Hemp%size_empty_inv.
        rewrite ->Hemp in Hpending. set_solver. }
      iThaw "Hclose". iApply "Hclose"; last by eauto with iFrame.
      iIntros "!> %i' %i %Hi %Hnotcur [%Hpend|Hdone]".
      - iLeft. iPureIntro. set_solver.
      - iRight. eauto. }
    wp_pures. iApply "HΦ". eauto with iFrame. }
  { (* loop invariant holds initially *)
    iFrame "Hi". rewrite /loop_inv.
    replace (uint.nat num - uint.nat 0%Z)%nat with (uint.nat num) by word.
    iClear "#". clear loop_inv lock_inv num Hlen.
    iInduction elems as [|x elems] "IH" using rev_ind; simpl.
    { done. }
    rewrite big_sepL_app big_sepL_singleton.
    rewrite big_sepL_app big_sepL_singleton.
    rewrite app_length /= Nat.add_0_r set_seq_add_L.
    change (uint.nat 0) with 0%nat. simpl.
    iDestruct "HPs" as "[HPs $]".
    rewrite [_ ∪ ∅]right_id_L -gset_disj_union; last first.
    { apply disjoint_singleton_r.
      rewrite elem_of_set_seq. lia. }
    iDestruct "Hpending" as "[Hpending $]".
    iApply ("IH" with "HPs Hpending"). }
  (* continuation after loop *)
  iIntros "_".
  wp_apply (acquire_spec with "Hlk").
  iIntros "[Hlocked Hinv]". wp_pures.
  wp_apply (wp_forBreak_cond' with "[-]"); first iNamedAccu.
  iIntros "!> Hloop". iNamed "Hloop".
  iDestruct "Hinv" as "[Hinv|Hinv]".
  { (* Supposedly we already took out everything, but now we have the token twice -- contradiction. *)
    iDestruct "Hinv" as (?) "[_ Htok2]".
    iDestruct (own_valid_2 with "Htok Htok2") as %[]. }
  iNamed "Hinv".
  wp_load. wp_pures.
  case_bool_decide as Hleft; wp_pures.
  { (* Not yet done, once more around the loop. *)
    wp_apply (wp_condWait with "[$Hcond $Hlk $Hlocked Hnleft HPQ]").
    { rewrite /lock_inv. eauto 10 with iFrame. }
    iIntros "[Hlocked Hinv]". wp_pures.
    eauto 10 with iFrame. }
  iModIntro. iRight. iSplit; first done.
  wp_apply (release_spec with "[$Hlk $Hlocked Hnleft Htok]").
  { rewrite /lock_inv. iLeft. eauto 10 with iFrame. }
  wp_pures. iApply "HΦ".
  iApply (big_sepL_impl with "HPQ").
  iIntros "!> !> %i' %i %Hlk [%Hpending|[_ $]]".
  exfalso.
  apply Znot_lt_ge in Hleft.
  change (uint.Z 0) with 0 in Hleft.
  assert (uint.nat nleft = 0%nat) as Hnotleft by word.
  rewrite Hnotleft in Hsz.
  apply size_empty_inv in Hsz.
  set_solver.
Qed.

End goose_lang.
