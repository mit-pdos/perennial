From Coq Require Import ssreflect.
From stdpp Require Import gmap fin_sets.
From Perennial.Helpers Require Import Integers.

Definition rangeSet (start sz: Z): gset u64 :=
  list_to_set (U64 <$> seqZ start sz).

Lemma elem_of_seq start sz :
  ∀ i, i ∈ seq start sz ↔ (start ≤ i < start + sz)%nat.
Proof.
  intros i.
  rewrite elem_of_list_In in_seq.
  auto.
Qed.

Lemma elem_of_seqZ start sz :
  ∀ i, i ∈ seqZ start sz ↔ start ≤ i < start + sz.
Proof.
  intros i.
  rewrite /seqZ.
  rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_seq.
  split; intros.
  - destruct H as [y [-> Hin]]; lia.
  - exists (Z.to_nat (i - start)); lia.
Qed.

Theorem rangeSet_lookup (start sz: Z) (i: u64) :
  0 ≤ start →
  start + sz < 2^64 →
  i ∈ rangeSet start sz ↔ start ≤ int.val i < start + sz.
Proof.
  intros Hpos Hoverflow.
  rewrite /rangeSet.
  rewrite elem_of_list_to_set.
  rewrite elem_of_list_fmap.
  split; intros.
  - destruct H as [y [-> Hin%elem_of_seqZ]]; word.
  - exists (int.val i).
    split; [ word | ].
    apply elem_of_seqZ; word.
Qed.

(*
Lemma rangeSet_prepend (start sz k: nat) :
  Z.of_nat (start + S sz) < 2^64 ->
  (k = start + sz)%nat ->
  <[U64 start:=()]> (rangeSet (S start) sz) =
  <[U64 k:=()]> (rangeSet start sz).
Proof.
  intros Hoverflow ->.
  change (<[U64 start:=()]> (rangeSet (S start) sz)) with
      (rangeSet start (S sz)).
  apply map_eq; intros.
  destruct (decide (i = (start+sz)%nat)); subst.
  - rewrite lookup_insert.
    rewrite rangeSet_lookup_Some_1; try word; auto.
  - rewrite -> lookup_insert_ne by auto.
    rewrite -> !rangeSet_lookup by lia.
    repeat match goal with
           | |- context[decide ?P] => destruct (decide P)
           end; intuition; try word.
    contradiction n.
    word.
Qed.

Lemma rangeSet_insert_one:
  ∀ start sz i : u64,
    int.val start + int.val sz < 2^64 ->
    int.val i < int.val start + int.val sz
    → int.val start ≤ int.val i
    → rangeSet (int.nat start) (S (int.nat i - int.nat start)) =
      <[i:=()]> (rangeSet (int.nat start) (int.nat i - int.nat start)).
Proof.
  intros start sz i Hoverflow Hibound Hilower_bound.
  apply map_eq; intros k.
  destruct (decide (k = i)); subst.
  - rewrite lookup_insert.
    rewrite rangeSet_lookup_Some_1; try word; auto.
  - rewrite -> lookup_insert_ne by auto.
    rewrite -> !rangeSet_lookup by lia.
    repeat match goal with
           | |- context[decide ?P] => destruct (decide P)
           end; intuition; try word.
    contradiction n.
    word.
Qed.
*)

(* TODO: upstream this *)
Lemma gset_eq `{Countable A} (c1 c2: gset A) :
  (forall (x:A), x ∈ c1 ↔ x ∈ c2) → c1 = c2.
Proof.
  intros Hexteq.
  destruct c1 as [c1], c2 as [c2].
  f_equal.
  apply map_eq.
  rewrite /elem_of /gset_elem_of/mapset.mapset_elem_of /= in Hexteq.
  intros.
  destruct (c1 !! i) eqn:Hc1;
    destruct (c2 !! i) eqn:Hc2; auto.
  - destruct u, u0; auto.
  - destruct u; apply Hexteq in Hc1.
    congruence.
  - destruct u; apply Hexteq in Hc2.
    congruence.
Qed.

Lemma gset_elem_is_empty `{Countable A} (c:gset A) :
  (forall x, x ∉ c) →
  c = ∅.
Proof.
  intros Hnoelem.
  apply gset_eq; intros.
  split; intros Helem.
  - contradiction (Hnoelem x).
  - contradiction (not_elem_of_empty (C:=gset A) x).
Qed.

Lemma rangeSet_diag (start sz: Z) :
  sz = 0 ->
  rangeSet start sz = ∅.
Proof.
  intros.
  rewrite /rangeSet.
  rewrite H.
  auto.
Qed.

(*
Theorem wp_freeRange (start sz: u64) :
  int.val start + int.val sz < 2^64 ->
  {{{ True }}}
    freeRange #start #sz
  {{{ (mref: loc), RET #mref;
      is_map mref (rangeSet (int.nat start) (int.nat sz)) }}}.
Proof.
  iIntros (Hbound Φ) "_ HΦ".
  wp_call.
  wp_apply (wp_NewMap () (t:=struct.t unit.S)).
  iIntros (mref) "Hmap".
  wp_apply wp_ref_to; first by val_ty.
  iIntros (il) "i".
  wp_pures.
  wp_apply (wp_forUpto (λ i, "%Hilower_bound" ∷ ⌜int.val start ≤ int.val i⌝ ∗
                             "Hmap" ∷ is_map mref (rangeSet (int.nat start) (int.nat i - int.nat start)%nat))%I
            with "[] [Hmap $i]").
  - word.
  - clear Φ.
    iIntros (i).
    iIntros "!>" (Φ) "(HI & i & %Hibound) HΦ"; iNamed "HI".
    wp_pures.
    wp_load.
    wp_apply (wp_MapInsert _ _ _ _ () with "Hmap"); auto.
    iIntros "Hm".
    wp_pures.
    iApply "HΦ".
    iFrame.
    iSplitR.
    { iPureIntro; word. }
    rewrite /named.
    iExactEq "Hm".
    f_equal.
    replace (int.val (word.add start sz)) with (int.val start + int.val sz) in Hibound by word.
    replace (int.nat (word.add i 1)) with (S (int.nat i)) by word.
    replace (S (int.nat i) - int.nat start)%nat with (S (int.nat i - int.nat start)) by word.
    rewrite /map_insert.
    erewrite rangeSet_insert_one; eauto.

  - iSplitR; auto.
    rewrite -> rangeSet_diag by lia; auto.
  - iIntros "(HI&Hil)"; iNamed "HI".
    wp_pures.
    iApply "HΦ".
    iExactEq "Hmap".
    f_equal.
    f_equal.
    word.
Qed.
*)
