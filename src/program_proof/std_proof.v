From Perennial.Helpers Require Import List ModArith.

From Goose.github_com.goose_lang Require Import std.

From iris.algebra Require Import excl gset.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Class multiparG Σ :=
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

Lemma wp_BytesEqual (x y : Slice.t) (xs ys : list byte) qx qy :
  {{{ typed_slice.is_slice_small x byteT qx xs ∗
      typed_slice.is_slice_small y byteT qy ys }}}
    BytesEqual (slice_val x) (slice_val y)
  {{{ RET #(bool_decide (xs = ys));
      typed_slice.is_slice_small x byteT qx xs ∗
      typed_slice.is_slice_small y byteT qy ys }}}.
Proof.
  iIntros (Φ) "[Hx Hy] HΦ". wp_lam. wp_pures.
  do 2 wp_apply wp_slice_len.
  wp_pures.
  iDestruct (typed_slice.is_slice_small_sz with "Hx") as %Hxlen.
  iDestruct (typed_slice.is_slice_small_sz with "Hy") as %Hylen.
  assert (#x.(Slice.sz) = #(length xs))%V as ->.
  { rewrite Hxlen. do 2 f_equal. word. }
  assert (#y.(Slice.sz) = #(length ys))%V as ->.
  { rewrite Hylen. do 2 f_equal. word. }
  destruct_decide (bool_decide_reflect (#(length xs) = #(length ys))) as Hlen; last first.
  { (* Different lengths. *)
    wp_pures.
    case_bool_decide as Hsl.
    - subst ys. exfalso. apply Hlen. done.
    - iApply "HΦ". eauto with iFrame. }
  wp_pures.
  assert (length xs = length ys) as Hlens.
  { cut (Z.of_nat (length xs) = length ys).
    { intros ?%Z_of_nat_inj. done. }
    (* Coq "injection" is silly and applies injection recursively without control... *)
    assert (∀ x y: u64, #(LitInt x) = #(LitInt y) → x = y) as Hinj.
    { clear. intros ?? [= ->]. done. }
    apply Hinj in Hlen. clear Hinj.
    apply word.of_Z_inj_small in Hlen; word. }
  clear Hlen.

  wp_apply wp_ref_to; first by val_ty.
  iIntros (l) "Hi". wp_pures.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (ret) "Hret". wp_pures.

  iApply (wp_frame_wand with "HΦ").

  (* Weaken for loop invariant *)
  iAssert (∃ i : nat, ⌜i < 2^64⌝ ∗ l ↦[uint64T] #i ∗ ret ↦[boolT] #(bool_decide (take i xs = take i ys)))%I with "[Hi Hret]" as "Hinv".
  { iExists 0%nat. by iFrame. }

  wp_apply (wp_forBreak_cond' with "[-]"); first by iNamedAccu.
  iIntros "!# HP". iNamed "HP".
  iDestruct "Hinv" as (i ?) "[Hi Hret]".
  wp_pures.
  wp_load.
  wp_if_destruct; last first.
  { (* i >= length *)
    assert (int.Z (length xs) ≤ int.Z i) as Hle by lia. clear Heqb.
    (* FIXME: can't some automation do this? *)
    replace (int.Z i) with (Z.of_nat i) in Hle by word.
    replace (int.Z (length xs)) with (Z.of_nat (length xs)) in Hle by word.
    apply Nat2Z.inj_le in Hle.
    iRight. iModIntro. iSplit; first done. wp_load.
    rewrite firstn_all2 //.
    rewrite firstn_all2; last by rewrite -Hlens.
    iIntros "!> HΦ". iApply "HΦ". eauto with iFrame. }
  wp_pures.
  replace (int.Z i) with (Z.of_nat i) in Heqb by word.
  replace (int.Z (length xs)) with (Z.of_nat (length xs)) in Heqb by word.
  apply Nat2Z.inj_lt in Heqb.
  destruct (lookup_lt_is_Some_2 xs i) as [xi Hxi]; first done.
  destruct (lookup_lt_is_Some_2 ys i) as [yi Hyi]; first by rewrite -Hlens.
  wp_load.
  (* FIXME: some typeclass is set up wrong so TC inference picks the wrong type here *)
  wp_apply (typed_slice.wp_SliceGet (V:=u8) with "[$Hx]").
  { replace (int.nat i) with i by word. done. }
  iIntros "Hx".
  wp_load.
  wp_apply (typed_slice.wp_SliceGet (V:=u8) with "[$Hy]").
  { replace (int.nat i) with i by word. done. }
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
    iFrame. iExists (S i).
    iSplit.
    { iPureIntro. word. }
    replace (word.add i 1) with (U64 (S i)) by word.
    iFrame.
    case_bool_decide as Heq.
    + rewrite bool_decide_true; first done.
      apply list_eq. intros j.
      destruct (decide (j = i)) as [->|Hne].
      * rewrite !lookup_take; [|lia..].
        rewrite Hxi Hyi. done.
      * rewrite !take_S_lookup_ne //. by rewrite Heq.
    + rewrite bool_decide_false; first done.
      rename Heq into Hne. intros Heq. apply Hne.
      apply list_eq. intros j.
      destruct (decide (j = i)) as [->|Hne'].
      * rewrite lookup_take_ge. 2:lia.
        rewrite lookup_take_ge. 2:lia.
        done.
      * rewrite -take_S_lookup_ne //.
        rewrite -[take i ys !! _]take_S_lookup_ne //.
        rewrite Heq //.
Qed.

Lemma wp_SumAssumeNoOverflow (x y : u64) :
  ∀ Φ : val → iProp Σ,
    (⌜int.Z (word.add x y) = (int.Z x + int.Z y)%Z⌝ -∗ Φ #(LitInt $ word.add x y)) -∗
    WP SumAssumeNoOverflow #x #y {{ Φ }}.
Proof.
  iIntros "%Φ HΦ". wp_lam; wp_pures.
  wp_apply wp_Assume.
  rewrite bool_decide_eq_true.
  iIntros (<-%sum_nooverflow_l). wp_pures. iModIntro.
  iApply "HΦ". iPureIntro. done.
Qed.

Lemma wp_Multipar `{!multiparG Σ} (P Q : nat → iProp Σ) (num : u64) (op : val) :
  □(∀ i : u64, ⌜int.Z i < int.Z num⌝ -∗ P (int.nat i) -∗ WP op #i {{ _, Q (int.nat i) }}) -∗
  {{{ [∗ list] i ∈ seq 0 (int.nat num), P i }}}
    Multipar #num op
  {{{ RET #(); [∗ list] i ∈ seq 0 (int.nat num), Q i }}}.
Proof.
  iIntros "#Hop !> %Φ HPs HΦ". wp_lam.
  wp_apply wp_ref_to. { val_ty. }
  iIntros (nleft_l) "Hnleft". wp_pures.
  iMod (own_alloc (GSet (set_seq 0 (int.nat num)))) as (γpending) "Hpending".
  { done. }
  iMod (own_alloc (Excl ())) as (γtok) "Htok".
  { done. }
  set lock_inv := ( (∃ nleft : u64, nleft_l ↦[uint64T] #nleft ∗ own γtok (Excl ())) ∨
    ∃ (nleft : u64) (pending : gset nat),
      "%Hsz" ∷ ⌜size pending = int.nat nleft⌝ ∗
      "Hnleft" ∷ nleft_l ↦[uint64T] #nleft ∗
      "HPQ" ∷ ([∗ list] i ∈ seq 0 (int.nat num), ⌜i ∈ pending⌝ ∨ own γpending (GSet {[i]}) ∗ Q i)
      )%I.
  wp_apply (newlock_spec nroot _ lock_inv with "[Hnleft]").
  { iModIntro. rewrite /lock_inv. iRight.
    iExists num, (set_seq 0 (int.nat num)). iFrame. iSplit.
    - iPureIntro. rewrite -list_to_set_seq size_list_to_set ?seq_length //.
      apply NoDup_seq.
    - iApply big_sepL_intro. iIntros "!> %k %i %Hlk". iLeft. iPureIntro.
      apply elem_of_set_seq. apply lookup_seq in Hlk. lia. }
  iIntros (lk) "#Hlk". wp_pures.
  wp_apply (wp_newCond with "Hlk").
  iIntros (cond) "#Hcond". wp_pures.
  (* Loop starts *)
  wp_apply wp_ref_to. { val_ty. }
  iIntros (i_l) "Hi".
  set loop_inv := (λ cur : u64,
    [∗ list] i ∈ seq (int.nat cur) (int.nat num - int.nat cur)%nat, own γpending (GSet {[i]}) ∗ P i)%I.
  wp_apply (wp_forUpto loop_inv _ _ 0 with "[] [HPs Hpending Hi]").
  { word. }
  { clear Φ.
    iIntros "%cur !> %Φ (Hloop & Hcur & %Hcur) HΦ". wp_pures.
    wp_load.
    iAssert (loop_inv (word.add cur 1) ∗ own γpending (GSet {[int.nat cur]}) ∗ P (int.nat cur))%I with "[Hloop]"
      as "(Hloop & Hpending & HP)".
    { rewrite /loop_inv.
      replace (int.nat num - int.nat cur)%nat with (1 + (int.nat num - int.nat (word.add cur 1)))%nat by word.
      rewrite seq_app. simpl.
      iDestruct "Hloop" as "(($ & $) & Hloop)".
      replace (int.nat cur + 1)%nat with (int.nat (word.add cur 1)) by word.
      done. }
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
      iRight. iExists _, (pending ∖ {[int.nat cur]}). iFrame "Hnleft".
      iDestruct (big_sepL_lookup_acc_impl (int.nat cur) (int.nat cur) with "HPQ") as "[Hcur Hclose]".
      { rewrite lookup_seq. word. }
      iFreeze "Hclose".
      iDestruct "Hcur" as "[%Hpending|[Hpending2 _]]"; last first.
      { (* This index is supposedly already done -- contradiction. *)
        iDestruct (own_valid_2 with "Hpending Hpending2") as %Hval%gset_disj_valid_op.
        exfalso. set_solver. }
      iModIntro. iSplit.
      { iPureIntro. trans (size (pending) - size (C:=gset nat) ({[int.nat cur]}))%nat.
        - (* TODO use size_difference once upstream std++ MR 324 lands *)
          rewrite {2}(union_difference {[int.nat cur]} pending); last set_solver.
          rewrite size_union; last by set_solver+. lia.
        - rewrite Hsz size_singleton.
          assert (int.nat nleft ≠ 0%nat). 2:word.
          rewrite -Hsz. intros Hemp%size_empty_inv.
          rewrite ->Hemp in Hpending. set_solver. }
      iThaw "Hclose". iApply "Hclose"; last by eauto with iFrame.
      iIntros "!> %i' %i %Hi %Hnotcur [%Hpend|Hdone]".
      - iLeft. iPureIntro. apply lookup_seq in Hi as [-> ?]. set_solver.
      - iRight. eauto. }
    wp_pures. iApply "HΦ". eauto with iFrame. }
  { (* loop invariant holds initially *)
    iFrame "Hi". rewrite /loop_inv.
    replace (int.nat num - int.nat 0%Z)%nat with (int.nat num) by word.
    iClear "#". clear loop_inv lock_inv.
    change (int.nat 0) with 0%nat.
    remember 0%nat as start eqn:Hstart. clear Hstart.
    iInduction (int.nat num) as [|n] "IH" forall (start); clear num; simpl.
    { done. }
    iDestruct "HPs" as "[$ HPs]".
    rewrite -gset_disj_union; last first.
    { apply disjoint_singleton_l.
      rewrite elem_of_set_seq. lia. }
    iDestruct "Hpending" as "[$ Hpending]".
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
  iApply "HΦ".
  iApply (big_sepL_impl with "HPQ").
  iIntros "!> %i' %i %Hlk [%Hpending|[_ $]]".
  exfalso.
  apply Znot_lt_ge in Hleft.
  change (int.Z 0) with 0 in Hleft.
  assert (int.nat nleft = 0%nat) as Hnotleft by word.
  rewrite Hnotleft in Hsz.
  apply size_empty_inv in Hsz.
  set_solver.
Qed.

End goose_lang.
