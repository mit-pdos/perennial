From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.

Section common_proof.

Context `{!heapG Σ}.

Definition uNSHARD : Z := 65536%Z.

Definition shardOfC (key:u64) : u64 := (word.modu key uNSHARD).

Lemma shardOfC_bound k : int.Z (shardOfC k) < uNSHARD.
Proof.
  rewrite /shardOfC /uNSHARD.
  rewrite word.unsigned_modu_nowrap //.
  apply Z.mod_pos_bound. done.
Qed.

Lemma wp_shardOf key :
  {{{
       True
  }}}
    shardOf #key
  {{{
       RET #(shardOfC key); True
  }}}.
Proof.
  iIntros (?) "_ HΦ".
  wp_lam.
  wp_pures.
  by iApply "HΦ".
Qed.

Lemma wp_shardOf_bound (key:u64) :
  {{{
      True
  }}}
    shardOf #key
  {{{
     (s:u64), RET #s; ⌜int.Z s < uNSHARD⌝
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_shardOf; first done.
  iIntros "!> _". iApply "HΦ".
  iPureIntro. apply shardOfC_bound.
Qed.

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

Lemma wp_bytesEqual (x y : Slice.t) (xs ys : list byte) qx qy :
  {{{ typed_slice.is_slice_small x byteT qx xs ∗
      typed_slice.is_slice_small y byteT qy ys }}}
    bytesEqual (slice_val x) (slice_val y)
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

End common_proof.
